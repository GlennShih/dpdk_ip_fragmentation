/*-
 *   BSD LICENSE
 *
 *   Copyright(c) 2010-2014 Intel Corporation. All rights reserved.
 *   All rights reserved.
 *
 *   Redistribution and use in source and binary forms, with or without
 *   modification, are permitted provided that the following conditions
 *   are met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in
 *       the documentation and/or other materials provided with the
 *       distribution.
 *     * Neither the name of Intel Corporation nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 *   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *   "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *   LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *   A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *   OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *   SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *   LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *   DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *   THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *   (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *   OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include <stdio.h>
//#include <arpa/inet.h> //20170902 uint32_t to ipv4 address
#include <inttypes.h> //20170830 printf for uint32_t and uint16_t
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <sys/types.h>
#include <sys/param.h>
#include <string.h>
#include <sys/queue.h>
#include <stdarg.h>
#include <errno.h>
#include <getopt.h>

#include <rte_common.h>
#include <rte_byteorder.h>
#include <rte_log.h>
#include <rte_memory.h>
#include <rte_memcpy.h>
#include <rte_memzone.h>
#include <rte_eal.h>
#include <rte_per_lcore.h>
#include <rte_launch.h>
#include <rte_atomic.h>
#include <rte_cycles.h>
#include <rte_prefetch.h>
#include <rte_lcore.h>
#include <rte_per_lcore.h>
#include <rte_branch_prediction.h>
#include <rte_interrupts.h>
#include <rte_pci.h>
#include <rte_random.h>
#include <rte_debug.h>
#include <rte_ether.h>
#include <rte_ethdev.h>
#include <rte_mempool.h>
#include <rte_mbuf.h>
#include <rte_ip.h>
#include <rte_string_fns.h>

#include <rte_ip_frag.h>

#define RTE_LOGTYPE_IP_FRAG RTE_LOGTYPE_USER1

/* allow max jumbo frame 9.5 KB */
#define JUMBO_FRAME_MAX_SIZE	0x2600

#define	ROUNDUP_DIV(a, b)	(((a) + (b) - 1) / (b))

/*
 * Default byte size for the IPv4 Maximum Transfer Unit (MTU).
 * This value includes the size of IPv4 header.
 */
#define	IPV4_MTU_DEFAULT	ETHER_MTU

/*
 * Default payload in bytes for the IPv4 packet.
 */
#define	IPV4_DEFAULT_PAYLOAD	(IPV4_MTU_DEFAULT - sizeof(struct ipv4_hdr))

/*
 * Max number of fragments per packet expected - defined by config file.
 */
#define	MAX_PACKET_FRAG RTE_LIBRTE_IP_FRAG_MAX_FRAG

#define NB_MBUF   8192

#define MAX_PKT_BURST	32
#define BURST_TX_DRAIN_US 100 /* TX drain every ~100us */

/* Configure how many packets ahead to prefetch, when reading packets */
#define PREFETCH_OFFSET	3

/*
 * Configurable number of RX/TX ring descriptors
 */
#define RTE_TEST_RX_DESC_DEFAULT 128
#define RTE_TEST_TX_DESC_DEFAULT 512
static uint16_t nb_rxd = RTE_TEST_RX_DESC_DEFAULT;
static uint16_t nb_txd = RTE_TEST_TX_DESC_DEFAULT;

/* ethernet addresses of ports */
static struct ether_addr ports_eth_addr[RTE_MAX_ETHPORTS];

#ifndef IPv4_BYTES
#define IPv4_BYTES_FMT "%" PRIu8 ".%" PRIu8 ".%" PRIu8 ".%" PRIu8
#define IPv4_BYTES(addr) \
		(uint8_t) (((addr) >> 24) & 0xFF),\
		(uint8_t) (((addr) >> 16) & 0xFF),\
		(uint8_t) (((addr) >> 8) & 0xFF),\
		(uint8_t) ((addr) & 0xFF)
#endif


/* mask of enabled ports */
static int enabled_port_mask = 0;

static int rx_queue_per_lcore = 1;

#define MBUF_TABLE_SIZE  (2 * MAX(MAX_PKT_BURST, MAX_PACKET_FRAG))

struct mbuf_table {
	uint16_t len;
	struct rte_mbuf *m_table[MBUF_TABLE_SIZE];
};

struct rx_queue {
	struct rte_mempool *direct_pool;
	struct rte_mempool *indirect_pool;
	uint8_t portid;
};

#define MAX_RX_QUEUE_PER_LCORE 16
#define MAX_TX_QUEUE_PER_PORT 16
struct lcore_queue_conf {
	uint16_t n_rx_queue;
	uint16_t tx_queue_id[RTE_MAX_ETHPORTS];
	struct rx_queue rx_queue_list[MAX_RX_QUEUE_PER_LCORE];
	struct mbuf_table tx_mbufs[RTE_MAX_ETHPORTS];
} __rte_cache_aligned;
struct lcore_queue_conf lcore_queue_conf[RTE_MAX_LCORE];

static const struct rte_eth_conf port_conf = {
	.rxmode = {
		.max_rx_pkt_len = JUMBO_FRAME_MAX_SIZE,
		.split_hdr_size = 0,
		.header_split   = 0, /**< Header Split disabled */
		.hw_ip_checksum = 1, /**< IP checksum offload enabled */
		.hw_vlan_filter = 0, /**< VLAN filtering disabled */
		.jumbo_frame    = 1, /**< Jumbo Frame Support enabled */
		.hw_strip_crc   = 1, /**< CRC stripped by hardware */
	},
	.txmode = {
		.mq_mode = ETH_MQ_TX_NONE,
	},
};


static struct rte_mempool *socket_direct_pool[RTE_MAX_NUMA_NODES];
static struct rte_mempool *socket_indirect_pool[RTE_MAX_NUMA_NODES];

/*uint32_t to ip address function 20170904 */
void print_ip(int ip)
{
    unsigned char bytes[4];
    bytes[0] = ip & 0xFF;
    bytes[1] = (ip >> 8) & 0xFF;
    bytes[2] = (ip >> 16) & 0xFF;
    bytes[3] = (ip >> 24) & 0xFF;   
    printf("%d.%d.%d.%d\n", bytes[3], bytes[2], bytes[1], bytes[0]);        
}

static inline void
read_and_print_ipv4_info(struct rte_mbuf *m)
{

	/* Remove the Ethernet header and trailer from the input packet */
	rte_pktmbuf_adj(m, (uint16_t)sizeof(struct ether_hdr));

	/* if this is an IPv4 packet */
	if (RTE_ETH_IS_IPV4_HDR(m->packet_type)) {
		struct ipv4_hdr *ip_hdr;
        uint32_t ip_dst;
	    uint32_t ip_src; //20170830	
        uint16_t total_len; //20170902 16 bits unsign int total_length

    /* Read the ipv4 ip (i.e. ip_dst, ip_src) from the input packet */
		ip_hdr = rte_pktmbuf_mtod(m, struct ipv4_hdr *);

		ip_dst = rte_be_to_cpu_32(ip_hdr->dst_addr);
        printf("ip_dst: "); //20170904
        print_ip(ip_dst); //20170904 uint32_t to ip address

        ip_src = rte_be_to_cpu_32(ip_hdr->src_addr);//20170830        
        printf("ip_src: "); //20170904
        print_ip(ip_src); //20170904 uint32_t to ip address

        total_len = rte_cpu_to_be_16(ip_hdr->total_length);//20170831 rte_cpu_to_be_16
   
        //printf("ip_dst: ");
        //printf("%" PRIu32 "\n" ,ip_dst);//20170830
        //printf("ip_src: ");
        //printf("%" PRIu32 "\n" ,ip_src);//20170830
        printf("total_length: ");
        printf("%" PRIu16 "\n" ,total_len);//20170831
        printf("\n");       
 
	} 

}


/* main processing loop */
static int
main_loop(__attribute__((unused)) void *dummy)
{
	struct rte_mbuf *pkts_burst[MAX_PKT_BURST];
	unsigned lcore_id;
	int i, j, nb_rx;
	uint8_t portid;
	struct lcore_queue_conf *qconf;

	lcore_id = rte_lcore_id();
	qconf = &lcore_queue_conf[lcore_id];

	if (qconf->n_rx_queue == 0) {
		RTE_LOG(INFO, IP_FRAG, "lcore %u has nothing to do\n", lcore_id);
		return 0;
	}

	RTE_LOG(INFO, IP_FRAG, "entering main loop on lcore %u\n", lcore_id);

	for (i = 0; i < qconf->n_rx_queue; i++) {

		portid = qconf->rx_queue_list[i].portid;
		RTE_LOG(INFO, IP_FRAG, " -- lcoreid=%u portid=%d\n", lcore_id,
				(int) portid);
	}

	while (1) {

		/*
		 * Read packet from RX queues
		 */
		for (i = 0; i < qconf->n_rx_queue; i++) {

			portid = qconf->rx_queue_list[i].portid;
			nb_rx = rte_eth_rx_burst(portid, 0, pkts_burst,
						 MAX_PKT_BURST);

			/* Prefetch first packets */
			for (j = 0; j < PREFETCH_OFFSET && j < nb_rx; j++) {
				rte_prefetch0(rte_pktmbuf_mtod(
						pkts_burst[j], void *));
			}

			/* Prefetch and print already prefetched packets */
			for (j = 0; j < (nb_rx - PREFETCH_OFFSET); j++) {
				rte_prefetch0(rte_pktmbuf_mtod(pkts_burst[
						j + PREFETCH_OFFSET], void *));
				read_and_print_ipv4_info(pkts_burst[j]);
			}

			/* print remaining prefetched packets */
			for (; j < nb_rx; j++) {
				read_and_print_ipv4_info(pkts_burst[j]);
			}
		}
	}
}

/* display usage */
static void
print_usage(const char *prgname)
{
	printf("%s [EAL options] -- -p PORTMASK [-q NQ]\n"
	       "  -p PORTMASK: hexadecimal bitmask of ports to configure\n"
	       "  -q NQ: number of queue (=ports) per lcore (default is 1)\n",
	       prgname);
}

static int
parse_portmask(const char *portmask)
{
	char *end = NULL;
	unsigned long pm;

	/* parse hexadecimal string */
	pm = strtoul(portmask, &end, 16);
	if ((portmask[0] == '\0') || (end == NULL) || (*end != '\0'))
		return -1;

	if (pm == 0)
		return -1;

	return pm;
}

static int
parse_nqueue(const char *q_arg)
{
	char *end = NULL;
	unsigned long n;

	/* parse hexadecimal string */
	n = strtoul(q_arg, &end, 10);
	if ((q_arg[0] == '\0') || (end == NULL) || (*end != '\0'))
		return -1;
	if (n == 0)
		return -1;
	if (n >= MAX_RX_QUEUE_PER_LCORE)
		return -1;

	return n;
}

/* Parse the argument given in the command line of the application */
static int
parse_args(int argc, char **argv)
{
	int opt, ret;
	char **argvopt;
	int option_index;
	char *prgname = argv[0];
	static struct option lgopts[] = {
		{NULL, 0, 0, 0}
	};

	argvopt = argv;

	while ((opt = getopt_long(argc, argvopt, "p:q:",
				  lgopts, &option_index)) != EOF) {

		switch (opt) {
		/* portmask */
		case 'p':
			enabled_port_mask = parse_portmask(optarg);
			if (enabled_port_mask < 0) {
				printf("invalid portmask\n");
				print_usage(prgname);
				return -1;
			}
			break;

		/* nqueue */
		case 'q':
			rx_queue_per_lcore = parse_nqueue(optarg);
			if (rx_queue_per_lcore < 0) {
				printf("invalid queue number\n");
				print_usage(prgname);
				return -1;
			}
			break;

		/* long options */
		case 0:
			print_usage(prgname);
			return -1;

		default:
			print_usage(prgname);
			return -1;
		}
	}

	if (enabled_port_mask == 0) {
		printf("portmask not specified\n");
		print_usage(prgname);
		return -1;
	}

	if (optind >= 0)
		argv[optind-1] = prgname;

	ret = optind-1;
	optind = 0; /* reset getopt lib */
	return ret;
}

static void
print_ethaddr(const char *name, struct ether_addr *eth_addr)
{
	char buf[ETHER_ADDR_FMT_SIZE];
	ether_format_addr(buf, ETHER_ADDR_FMT_SIZE, eth_addr);
	printf("%s%s", name, buf);
}

/* Check the link status of all ports in up to 9s, and print them finally */
static void
check_all_ports_link_status(uint8_t port_num, uint32_t port_mask)
{
#define CHECK_INTERVAL 100 /* 100ms */
#define MAX_CHECK_TIME 90 /* 9s (90 * 100ms) in total */
	uint8_t portid, count, all_ports_up, print_flag = 0;
	struct rte_eth_link link;

	printf("\nChecking link status");
	fflush(stdout);
	for (count = 0; count <= MAX_CHECK_TIME; count++) {
		all_ports_up = 1;
		for (portid = 0; portid < port_num; portid++) {
			if ((port_mask & (1 << portid)) == 0)
				continue;
			memset(&link, 0, sizeof(link));
			rte_eth_link_get_nowait(portid, &link);
			/* print link status if flag set */
			if (print_flag == 1) {
				if (link.link_status)
					printf("Port %d Link Up - speed %u "
						"Mbps - %s\n", (uint8_t)portid,
						(unsigned)link.link_speed,
				(link.link_duplex == ETH_LINK_FULL_DUPLEX) ?
					("full-duplex") : ("half-duplex\n"));
				else
					printf("Port %d Link Down\n",
							(uint8_t)portid);
				continue;
			}
			/* clear all_ports_up flag if any link down */
			if (link.link_status == ETH_LINK_DOWN) {
				all_ports_up = 0;
				break;
			}
		}
		/* after finally printing all link status, get out */
		if (print_flag == 1)
			break;

		if (all_ports_up == 0) {
			printf(".");
			fflush(stdout);
			rte_delay_ms(CHECK_INTERVAL);
		}

		/* set the print_flag if all ports up or timeout */
		if (all_ports_up == 1 || count == (MAX_CHECK_TIME - 1)) {
			print_flag = 1;
			printf("\ndone\n");
		}
	}
}

/* Check L3 packet type detection capablity of the NIC port */
static int
check_ptype(int portid)
{
	int i, ret;
	int ptype_l3_ipv4 = 0;
	uint32_t ptype_mask = RTE_PTYPE_L3_MASK;

	ret = rte_eth_dev_get_supported_ptypes(portid, ptype_mask, NULL, 0);
	if (ret <= 0)
		return 0;

	uint32_t ptypes[ret];

	ret = rte_eth_dev_get_supported_ptypes(portid, ptype_mask, ptypes, ret);
	for (i = 0; i < ret; ++i) {
		if (ptypes[i] & RTE_PTYPE_L3_IPV4)
			ptype_l3_ipv4 = 1;
	}

	if (ptype_l3_ipv4 == 0)
		printf("port %d cannot parse RTE_PTYPE_L3_IPV4\n", portid);

	return 0;

}

/* Parse packet type of a packet by SW */
static inline void
parse_ptype(struct rte_mbuf *m)
{
	struct ether_hdr *eth_hdr;
	uint32_t packet_type = RTE_PTYPE_UNKNOWN;
	uint16_t ether_type;

	eth_hdr = rte_pktmbuf_mtod(m, struct ether_hdr *);
	ether_type = eth_hdr->ether_type;
	if (ether_type == rte_cpu_to_be_16(ETHER_TYPE_IPv4))
		packet_type |= RTE_PTYPE_L3_IPV4_EXT_UNKNOWN;

	m->packet_type = packet_type;
}

/* callback function to detect packet type for a queue of a port */
static uint16_t
cb_parse_ptype(uint8_t port __rte_unused, uint16_t queue __rte_unused,
		   struct rte_mbuf *pkts[], uint16_t nb_pkts,
		   uint16_t max_pkts __rte_unused,
		   void *user_param __rte_unused)
{
	uint16_t i;

	for (i = 0; i < nb_pkts; ++i)
		parse_ptype(pkts[i]);

	return nb_pkts;
}

static int
init_mem(void)
{
	char buf[PATH_MAX];
	struct rte_mempool *mp;
	int socket;
	unsigned lcore_id;

	/* traverse through lcores and initialize structures on each socket */

	for (lcore_id = 0; lcore_id < RTE_MAX_LCORE; lcore_id++) {

		if (rte_lcore_is_enabled(lcore_id) == 0)
			continue;

		socket = rte_lcore_to_socket_id(lcore_id);

		if (socket == SOCKET_ID_ANY)
			socket = 0;

		if (socket_direct_pool[socket] == NULL) {
			RTE_LOG(INFO, IP_FRAG, "Creating direct mempool on socket %i\n",
					socket);
			snprintf(buf, sizeof(buf), "pool_direct_%i", socket);

			mp = rte_pktmbuf_pool_create(buf, NB_MBUF, 32,
				0, RTE_MBUF_DEFAULT_BUF_SIZE, socket);
			if (mp == NULL) {
				RTE_LOG(ERR, IP_FRAG, "Cannot create direct mempool\n");
				return -1;
			}
			socket_direct_pool[socket] = mp;
		}

		if (socket_indirect_pool[socket] == NULL) {
			RTE_LOG(INFO, IP_FRAG, "Creating indirect mempool on socket %i\n",
					socket);
			snprintf(buf, sizeof(buf), "pool_indirect_%i", socket);

			mp = rte_pktmbuf_pool_create(buf, NB_MBUF, 32, 0, 0,
				socket);
			if (mp == NULL) {
				RTE_LOG(ERR, IP_FRAG, "Cannot create indirect mempool\n");
				return -1;
			}
			socket_indirect_pool[socket] = mp;
		}
	}

	return 0;
}

int
main(int argc, char **argv)
{
	struct lcore_queue_conf *qconf;
	struct rte_eth_dev_info dev_info;
	struct rte_eth_txconf *txconf;
	struct rx_queue *rxq;
	int socket, ret;
	unsigned nb_ports;
	uint16_t queueid = 0;
	unsigned lcore_id = 0, rx_lcore_id = 0;
	uint32_t n_tx_queue, nb_lcores;
	uint8_t portid;

	/* init EAL */
	ret = rte_eal_init(argc, argv);
	if (ret < 0)
		rte_exit(EXIT_FAILURE, "rte_eal_init failed");
	argc -= ret;
	argv += ret;

	/* parse application arguments (after the EAL ones) */
	ret = parse_args(argc, argv);
	if (ret < 0)
		rte_exit(EXIT_FAILURE, "Invalid arguments");

	nb_ports = rte_eth_dev_count();
	if (nb_ports == 0)
		rte_exit(EXIT_FAILURE, "No ports found!\n");

	nb_lcores = rte_lcore_count();

	/* initialize structures (mempools etc.) */
	if (init_mem() < 0)
		rte_panic("Cannot initialize memory structures!\n");

	/* check if portmask has non-existent ports */
	if (enabled_port_mask & ~(RTE_LEN2MASK(nb_ports, unsigned)))
		rte_exit(EXIT_FAILURE, "Non-existent ports in portmask!\n");

	/* initialize all ports */
	for (portid = 0; portid < nb_ports; portid++) {
		/* skip ports that are not enabled */
		if ((enabled_port_mask & (1 << portid)) == 0) {
			printf("Skipping disabled port %d\n", portid);
			continue;
		}

		qconf = &lcore_queue_conf[rx_lcore_id];

		/* get the lcore_id for this port */
		while (rte_lcore_is_enabled(rx_lcore_id) == 0 ||
		       qconf->n_rx_queue == (unsigned)rx_queue_per_lcore) {

			rx_lcore_id ++;
			if (rx_lcore_id >= RTE_MAX_LCORE)
				rte_exit(EXIT_FAILURE, "Not enough cores\n");

			qconf = &lcore_queue_conf[rx_lcore_id];
		}

		socket = (int) rte_lcore_to_socket_id(rx_lcore_id);
		if (socket == SOCKET_ID_ANY)
			socket = 0;

		rxq = &qconf->rx_queue_list[qconf->n_rx_queue];
		rxq->portid = portid;
		rxq->direct_pool = socket_direct_pool[socket];
		rxq->indirect_pool = socket_indirect_pool[socket];
		qconf->n_rx_queue++;

		/* init port */
		printf("Initializing port %d on lcore %u...", portid,
		       rx_lcore_id);
		fflush(stdout);

		n_tx_queue = nb_lcores;
		if (n_tx_queue > MAX_TX_QUEUE_PER_PORT)
			n_tx_queue = MAX_TX_QUEUE_PER_PORT;
		ret = rte_eth_dev_configure(portid, 1, (uint16_t)n_tx_queue,
					    &port_conf);
		if (ret < 0) {
			printf("\n");
			rte_exit(EXIT_FAILURE, "Cannot configure device: "
				"err=%d, port=%d\n",
				ret, portid);
		}

		/* init one RX queue */
		ret = rte_eth_rx_queue_setup(portid, 0, nb_rxd,
					     socket, NULL,
					     socket_direct_pool[socket]);
		if (ret < 0) {
			printf("\n");
			rte_exit(EXIT_FAILURE, "rte_eth_rx_queue_setup: "
				"err=%d, port=%d\n",
				ret, portid);
		}

		rte_eth_macaddr_get(portid, &ports_eth_addr[portid]);
		print_ethaddr(" Address:", &ports_eth_addr[portid]);
		printf("\n");

		/* init one TX queue per couple (lcore,port) */
		queueid = 0;
		for (lcore_id = 0; lcore_id < RTE_MAX_LCORE; lcore_id++) {
			if (rte_lcore_is_enabled(lcore_id) == 0)
				continue;

			socket = (int) rte_lcore_to_socket_id(lcore_id);
			printf("txq=%u,%d ", lcore_id, queueid);
			fflush(stdout);

			rte_eth_dev_info_get(portid, &dev_info);
			txconf = &dev_info.default_txconf;
			txconf->txq_flags = 0;
			ret = rte_eth_tx_queue_setup(portid, queueid, nb_txd,
						     socket, txconf);
			if (ret < 0) {
				printf("\n");
				rte_exit(EXIT_FAILURE, "rte_eth_tx_queue_setup: "
					"err=%d, port=%d\n", ret, portid);
			}

			qconf = &lcore_queue_conf[lcore_id];
			qconf->tx_queue_id[portid] = queueid;
			queueid++;
		}

		printf("\n");
	}

	printf("\n");

	/* start ports */
	for (portid = 0; portid < nb_ports; portid++) {
		if ((enabled_port_mask & (1 << portid)) == 0) {
			continue;
		}
		/* Start device */
		ret = rte_eth_dev_start(portid);
		if (ret < 0)
			rte_exit(EXIT_FAILURE, "rte_eth_dev_start: err=%d, port=%d\n",
				ret, portid);

		rte_eth_promiscuous_enable(portid);

		if (check_ptype(portid) == 0) {
			rte_eth_add_rx_callback(portid, 0, cb_parse_ptype, NULL);
			printf("Add Rx callback funciton to detect L3 packet type by SW :"
				" port = %d\n", portid);
		}
	}

	check_all_ports_link_status((uint8_t)nb_ports, enabled_port_mask);

	/* launch per-lcore init on every lcore */
	rte_eal_mp_remote_launch(main_loop, NULL, CALL_MASTER);
	RTE_LCORE_FOREACH_SLAVE(lcore_id) {
		if (rte_eal_wait_lcore(lcore_id) < 0)
			return -1;
	}

	return 0;
}
