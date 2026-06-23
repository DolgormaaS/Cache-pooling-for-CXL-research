import math
import random
import sys
import os

# system config
CACHE_BLOCK_SIZE = 64
MEM_SIZE = 8 << 30

# secure memroy config
COUNTER_ARITY = 64
BMT_ARITY = 8
MAC_ARITY = 8

# for capulet
all_caches = []

class Cache:
    class Block:
        def __init__(self):
            self.tag = -1
            self.lru = -1
            self.cache_id = -1     ########################## Cache ID to differentiate between local and remote cache

    def __init__(self, size, assoc):
        self.size = size
        self.assoc = assoc
        self.num_sets = size // CACHE_BLOCK_SIZE // assoc
        self.blocks = [[self.Block() for _ in range(assoc)] for _ in range(self.num_sets)]
        self.num_accesses = 0
        self.num_hits = 0
        self.num_misses = 0
        self.num_read_hits = 0
        self.num_write_hits = 0
        self.num_read_misses = 0
        self.num_write_misses = 0
        self.num_writebacks = 0
        self.num_invalidates = 0
        self.last_remote = 0           ##################### last remote cache to send the evicted address
        self.accepting_remote = True

        self.addrs_to_offer = []

    def get_idx(self, addr):
        return addr >> int(math.log(CACHE_BLOCK_SIZE, 2)) & (self.num_sets - 1)

    def get_tag(self, addr):
        #return addr >> int(math.log(CACHE_BLOCK_SIZE, 2) + math.log(CACHE_BLOCK_SIZE, 2))
        return addr >> int(math.log(CACHE_BLOCK_SIZE, 2) + math.log(self.num_sets, 2))    ######## Might be some mismatch happening

    def lookup(self, addr, cache_id):

        idx = self.get_idx(addr)
        for blk in self.blocks[idx]:
            if blk.tag == self.get_tag(addr) and blk.cache_id == cache_id:
                
                return True

        return False

    def access(self, addr, read):
        self.num_accesses += 1

        idx = self.get_idx(addr)
        for blk in self.blocks[idx]:
            if blk.tag == self.get_tag(addr) and blk.cache_id == all_caches.index(self):
                blk.lru = self.num_accesses
                self.num_hits += 1
                if read:
                    self.num_read_hits += 1
                else:
                    self.num_write_hits += 1

                if self.num_misses / self.num_accesses >= 0.5:
                    self.accepting_remote = True
                else:
                    self.accepting_remote = False

                return True

        self.num_misses += 1
        if read:
            self.num_read_misses += 1
        else:
            self.num_write_misses += 1

        if self.num_misses / self.num_accesses >= 0.5:
            self.accepting_remote = True
        else:
            self.accepting_remote = False

        return False

    def fill(self, addr, cache_id, is_remote=False):
        idx = self.get_idx(addr)
        lru = self.blocks[idx][0]
        host_num = all_caches.index(self)
        
        for blk in self.blocks[idx]:
            if blk.tag == -1:
                blk.tag = self.get_tag(addr)     ################## This was only updating tag before
                blk.lru = self.num_accesses
                blk.cache_id = cache_id
                return
            elif blk.lru < lru.lru:
                lru = blk
                self.num_writebacks += 1

        if self.capulet and not is_remote:
            evicted_addr = (lru.tag << int(math.log(self.num_sets, 2)) | idx) << int(math.log(CACHE_BLOCK_SIZE, 2))   ###################### addr to evicted_addr
            #r = 0 if len(all_caches) == 1 else random.randint(0, len(all_caches) - 1)          ########################### Old eviction policy
            #if all_caches[r] != self: #and random.randint(0, 1) == 1:
            #    print(f"Evicting to {r}")
            #    self.broadcast_offers += 1
            #    all_caches[r].fill(evicted_addr)
    
            for i in range(len(all_caches)):    ########## IF MISS RATE OF REMOTE HOST IS >=50, EVICT THE ADDRESS TO THAT HOST
                r = (self.last_remote + i) % len(all_caches)
                #current_host_miss_rates = 0
                #if all_caches[r].num_misses + all_caches[r].num_hits == 0:
                #    current_host_miss_rates = 100
                #else:
                #    current_host_miss_rates = all_caches[r].num_misses * 100 / (all_caches[r].num_misses + all_caches[r].num_hits)
                if all_caches[r] != self and all_caches[r].accepting_remote:
                    print(f"Evicting {cache_id} from {host_num}, to {r}.")
                    self.broadcast_offers += 1
                    all_caches[r].fill(evicted_addr, cache_id, is_remote = True)
                    self.last_remote = r + 1
                    break

        else:
            print(f"Caching {cache_id} to remote host {host_num}.")

        lru.tag = self.get_tag(addr)
        lru.lru = self.num_accesses
        lru.cache_id = cache_id
        return

class MetadataCache(Cache):
    def __init__(self, range_start, range_end, capulet=False):
        self.range_start = range_start
        self.range_end = range_end
        self.integrity_levels = [range_start]
        metadata_blocks_on_level = (range_end - range_start) // CACHE_BLOCK_SIZE // COUNTER_ARITY
        level_start = range_end
        while True:
            self.integrity_levels = [level_start] + self.integrity_levels
            level_start += metadata_blocks_on_level * CACHE_BLOCK_SIZE

            if metadata_blocks_on_level > 1:
                metadata_blocks_on_level //= BMT_ARITY
            else:
                break

        self.capulet = capulet
        self.hits = [0 for _ in self.integrity_levels]
        self.remote_hits = [0 for _ in self.integrity_levels]
        self.misses = [0 for _ in self.integrity_levels]
        print(f'integrity_levels: {self.integrity_levels}\nnum levels: {len(self.integrity_levels) -1}')

        self.broadcast_offers = 0
        self.broadcast_misses = 0
        self.broadcast_found = 0
        self.broadcast_invalidates = 0

        super(MetadataCache, self).__init__(64 << 10, 4)      ############################## LET'S TRY SHRINKING THE METADATA CACHE SIZE TO FORCE FREQUENT EVICTIONS TO SEE IF MY EVICTION THING IS ACTUALLY WORKING
        #super(MetadataCache, self).__init__(1 << 10, 4)

    def calculate_mac_addr(self, addr):
        return ((addr - self.range_start) // CACHE_BLOCK_SIZE) + self.integrity_levels[0] + CACHE_BLOCK_SIZE

    def calculate_counter_addr(self, addr):
        return ((addr - self.range_start) // COUNTER_ARITY) + self.integrity_levels[-2]

    def calculate_parent_addr(self, addr, level):
        assert level != 0
        idx_on_level = (addr - self.integrity_levels[level]) // CACHE_BLOCK_SIZE
        parent_idx = idx_on_level // BMT_ARITY

        if level != 1:
            return self.integrity_levels[level - 1] + (parent_idx * CACHE_BLOCK_SIZE)
        else:
            return self.integrity_levels[0]

    def data_read_write(self, addr, read):
        mac_addr = self.calculate_mac_addr(addr)
        ctr_addr = self.calculate_counter_addr(addr)
        cache_id = all_caches.index(self)

        if not self.access(mac_addr, read):
            self.misses[-1] += 1
            self.fill(mac_addr, cache_id)
        else:
            self.hits[-1] += 1

        num_iter = 2
        if read:
            num_iter = 1

        for i in range(num_iter):
            metadata_addr = ctr_addr
            to_fill = []
            for level in range(len(self.integrity_levels) - 1)[::-1]:
                if metadata_addr == self.integrity_levels[0]:
                    # reached the root
                    break
                elif self.access(metadata_addr, read or i == 0):
                    # trusted value
                    self.hits[level] += 1
                    if read:
                        break         ############################### ?
                else:
                    self.misses[level] += 1
                    if self.capulet and read:        ################################# ?
                        self.broadcast_misses += 1
                        remote_hit = False
                        for cache in all_caches:
                            if cache == self:     
                                continue
                            if cache.lookup(metadata_addr, cache_id):    
                                remote_hit = True
                                break
                        if remote_hit:
                            # remote hit
                            self.remote_hits[level] += 1
                            self.broadcast_found += 1
                            break

                    to_fill.append(metadata_addr)

                metadata_addr = self.calculate_parent_addr(metadata_addr, level)

            for miss_addr in to_fill:
                if read:
                    self.broadcast_invalidates += 1
                self.fill(miss_addr, cache_id)


    #def data_read(self, addr):
    #    mac_addr = self.calculate_mac_addr(addr)
    
    #    ctr_addr = self.calculate_counter_addr(addr)
    #    cache_id = all_caches.index(self)

    #    if not self.access(mac_addr, True):
    #        self.misses[-1] += 1
    #        self.fill(mac_addr, cache_id)
    #    else:
    #        self.hits[-1] += 1


    #    metadata_addr = ctr_addr
    #    to_fill = []
    #    for level in range(len(self.integrity_levels) - 1)[::-1]:
    #        if metadata_addr == self.integrity_levels[0]:
    #            # reached the root
    #            break
    #        elif self.access(metadata_addr, True):
    #            # trusted value
    #            self.hits[level] += 1
    #            break
    #        else:
    #            self.misses[level] += 1
    #            if self.capulet:
    #                self.broadcast_misses += 1
    #                remote_hit = False
    #                for cache in all_caches:
    #                    if cache == self:          ############################ no remote hit when it's looking the remote data from itself 
    #                        continue
    #                    if cache.lookup(metadata_addr, cache_id):        ########################## addr to metadata_addr
    #                        remote_hit = True
    #                        #exit(0)                  ###################### WHYYYYYYYYYYYYYYYYYYYYY
    #                        break
    #                if remote_hit:
    #                    # remote hit
    #                    self.remote_hits[level] += 1
    #                    self.broadcast_found += 1
    #                    break

    #            to_fill.append(metadata_addr)

    #        metadata_addr = self.calculate_parent_addr(metadata_addr, level)

    #    for miss_addr in to_fill:
    #        self.broadcast_invalidates += 1
    #        self.fill(miss_addr, cache_id)

    #def data_write(self, addr):
    #    mac_addr = self.calculate_mac_addr(addr)
    #    ctr_addr = self.calculate_counter_addr(addr)
    #    cache_id = all_caches.index(self)

    #    if not self.access(mac_addr, False):
    #        self.misses[-1] += 1
    #        self.fill(mac_addr, cache_id)
    #    else:
    #        self.hits[-1] += 1

    #    for x in range(2):
    #        metadata_addr = ctr_addr
    #        to_fill = []
    #        for level in range(len(self.integrity_levels) - 1)[::-1]:
    #            if metadata_addr == self.integrity_levels[0]:
    #                # reached the root
    #                break
    #            elif self.access(metadata_addr, True if x == 0 else False):
    #                # trusted value
    #                self.hits[level] += 1
    #            else:
    #                self.misses[level] += 1
    #                to_fill.append(metadata_addr)

    #            metadata_addr = self.calculate_parent_addr(metadata_addr, level)

    #        for miss_addr in to_fill:
    #            self.fill(miss_addr, cache_id)

class Host:
    def __init__(self, workload, range_start, range_end, data_accesses, capulet=False):
        self.workload = workload
        self.range_start = range_start
        self.range_end = range_end
        self.data_accesses = data_accesses
        self.total_data_accesses = data_accesses
        self.metadata_cache = MetadataCache(range_start, range_end, capulet=capulet)

        # for trace based simulation
        if workload != 'random':
            self.f = open(workload, 'r')
            line = self.f.readline()
            while 'REAL SIMULATION' not in line:
                line = self.f.readline()
            self.next_access = self.f.readline()

    def do_work(self):
        if self.workload == 'random':
            while self.data_accesses > 0:
                a = random.randint(self.range_start, self.range_end)
                #self.metadata_cache.data_read(a)
                self.metadata_cache.data_read_write(a, True)
                self.data_accesses -= 1
        else:
            while self.next_access != '':
                time, read, addr, _ = self.next_access.split(',')
                if read == '1':
                    #self.metadata_cache.data_read(addr + self.range_start)
                    self.metadata_cache.data_read_write(addr + self.range_start, True)
                else:
                    #self.metadata_cache.data_write(addr + self.range_start)
                    self.metadata_cache.data_read_write(addr + self.range_start, False)

                self.total_data_accesses += 1
                self.next_access = self.f.readline()

    def do_work_item(self):
        if self.workload == 'random':
            if self.data_accesses > 0:
                a = random.randint(self.range_start, self.range_end)
                #if self.data_accesses % 10000 == 0:
                #    print(f'accessing data address {a} on access {self.total_data_accesses - self.data_accesses}')
                self.metadata_cache.data_read(a)         ################################### SHOULD I ALSO DO FOR data_write()?
                self.data_accesses -= 1
        else:
            if self.next_access != '':
                time, read, addr, _ = self.next_access.split(',')
                #if self.total_data_accesses % 10000 == 0:
                #    print(f'accessing data address {addr} on access {self.total_data_accesses}')
                if read == '1':
                    #self.metadata_cache.data_read(int(addr) - (2 << 30))
                    self.metadata_cache.data_read_write(int(addr) - (2 << 30), True)
                else:
                    #self.metadata_cache.data_write(int(addr) - (2 << 30))
                    self.metadata_cache.data_read_write(int(addr) - (2 << 30), False)

                self.total_data_accesses += 1
                self.next_access = self.f.readline()

class CAPULET:
    def __init__(self, num_hosts, workloads):
        global all_caches
        self.hosts = []
        all_lines = []

        if num_hosts == len(workloads):
            i = 0
            for workload in workloads:
                self.hosts.append(Host(workload, MEM_SIZE * i * 2, (MEM_SIZE * i * 2) + MEM_SIZE, 0, capulet=True))
                i += 1

        elif num_hosts <= len(workloads):
            #1 or more hosts run 1 or more workloads
            workloads_per_host = int(len(workloads) / num_hosts)
            additional_workloads = int(len(workloads) % num_hosts)

            for i in range(num_hosts):
                amount_workloads = workloads_per_host
                if additional_workloads != 0:
                    amount_workloads += 1
                    additional_workloads -= 1

                read_workloads = workloads[:amount_workloads]

                for workload in read_workloads: 
                    with open(workload, 'r') as file:
                        lines = file.readlines()
                        header_end = 0
                        for r, line in enumerate(lines):
                            if 'REAL SIMULATION' in line:
                                header_end = r + 1
                                break
                        all_lines.extend(lines[header_end:])

                temporary = f'temporary_{i}.txt'
                with open(temporary, 'w') as file:
                    file.write('REAL SIMULATION\n')
                    file.writelines(all_lines)
                    self.hosts.append(Host(temporary, MEM_SIZE * i * 2, (MEM_SIZE * i * 2) + MEM_SIZE, 0, capulet=True))

                workloads = workloads[amount_workloads:]
                all_lines.clear()

        else:
            #multiple hosts share same file: Chunking is useful here.
            hosts_per_workload = int(num_hosts / len(workloads))
            additional_hosts = int(num_hosts % len(workloads))
            last_host = 0

            for workload in workloads:
                amount_hosts = hosts_per_workload
                if additional_hosts != 0:
                    amount_hosts += 1
                    additional_hosts -= 1
             
                with open(workload, 'r') as file:
                    lines = file.readlines()
                    header_end = 0
                    for i, line in enumerate(lines):
                        if 'REAL SIMULATION' in line:
                            header_end = i + 1
                            break
                    all_lines.extend(lines[header_end:]) 

                chunk_size = math.ceil(len(all_lines) / amount_hosts)

                for i in range(last_host, amount_hosts + last_host):
                    r = i - last_host
                    chunk = all_lines[chunk_size * r : chunk_size * (r + 1)]
                    if not chunk:
                        break

                    temporary = f'temporary_{i}.txt'
                    with open(temporary, 'w') as file:
                        file.write('REAL SIMULATION\n')
                        file.writelines(chunk)
                    self.hosts.append(Host(temporary, MEM_SIZE * i * 2, (MEM_SIZE * i * 2) + MEM_SIZE, 0, capulet=True))
                all_lines.clear()
                last_host  = amount_hosts + last_host


        #for i, workload in enumerate(workloads):
        #    self.hosts.append(Host(workload, MEM_SIZE * i * 2, (MEM_SIZE * i * 2) + MEM_SIZE, 100 if workload == 'random' else 0, capulet=True))   ############################## WORKLOAD 100
        #for workload in workloads:
        #    with open(workload, 'r') as file:
        #        lines = file.readlines()
        #        header_end = 0
        #        for i, line in enumerate(lines):
        #            if 'REAL SIMULATION' in line:
        #                header_end = i + 1
        #                break
        #        all_lines.extend(lines[header_end:])
        
        ##chunk_size = math.ceil(len(trace_lines) / num_hosts)
        #chunk_size = math.ceil(len(all_lines) / num_hosts)

        #for i in range(num_hosts):
        #    #chunk = trace_lines[chunk_size * i : chunk_size * (i + 1)]
        #    chunk = all_lines[chunk_size * i : chunk_size * (i + 1)]
        #    if not chunk:
        #        break
            
        #    temporary = f'temporary_{i}.txt'
        #    with open(temporary, 'w') as file:
        #        file.write('REAL SIMULATION\n')
        #        file.writelines(chunk)
        #    self.hosts.append(Host(temporary, MEM_SIZE * i * 2, (MEM_SIZE * i * 2) + MEM_SIZE, 0, capulet=True))



        self.all_hosts = self.hosts[:]

        all_caches = [host.metadata_cache for host in self.all_hosts]

    def do_work(self):
        while len(self.hosts) > 0:
            next_host = self.hosts[0]
            for host in self.hosts:
                if int(host.next_access.split(',')[0]) < int(next_host.next_access.split(',')[0]):
                    next_host = host

            for _ in range(random.randint(1, 50000)):         ####################################### OG 1, 50000
                next_host.do_work_item()
                if next_host.next_access == '' or next_host.total_data_accesses >= 1000000:
                    self.hosts.remove(next_host)
                    break


    def do_random_work(self):
        while len(self.hosts) > 0:
            for host in self.hosts:
                if host.data_accesses > 0:
                    host.do_work_item()
                else:
                    self.hosts.remove(host)

    def dump_stats(self):
        total_traffic = 0
        offer_traffic = 0
        miss_traffic = 0
        found_traffic = 0
        invalidate_traffic = 0

        if not os.path.isfile('stats.txt'):
            f = open('stats.txt', 'w')

        f = open('stats.txt', 'w')        ###################################### remove TOP_DIR

        for i in range(len(self.all_hosts)):
            host = self.all_hosts[i]
            hit_rate = sum(host.metadata_cache.hits) / (sum(host.metadata_cache.hits) + sum(host.metadata_cache.misses))
            read_hit_rate = host.metadata_cache.num_read_hits / (host.metadata_cache.num_read_hits + host.metadata_cache.num_read_misses)
            if host.metadata_cache.num_write_hits + host.metadata_cache.num_write_misses != 0:
                write_hit_rate = host.metadata_cache.num_write_hits / (host.metadata_cache.num_write_hits + host.metadata_cache.num_write_misses)         #################################### Uncommented this
            else:
                write_hit_rate = 0.

            avg_auth_path = (sum(host.metadata_cache.hits) + sum(host.metadata_cache.misses)) / host.total_data_accesses
            print(f'\nFinal stats dump for host {i}:\nhit rate:\t{hit_rate}\nread hit rate:\t{read_hit_rate}\nwrite hit rate:\t{write_hit_rate}\nhits:\t{host.metadata_cache.hits}\nmisses:\t{host.metadata_cache.misses}')
            f.write(f'\nFinal stats dump for host {i}:\nhit rate:\t{hit_rate}\nread hit rate:\t{read_hit_rate}\nwrite hit rate:\t{write_hit_rate}\nhits:\t{host.metadata_cache.hits}\nmisses:\t{host.metadata_cache.misses}')
            total_traffic += host.metadata_cache.broadcast_offers
            offer_traffic += host.metadata_cache.broadcast_offers
            total_traffic += host.metadata_cache.broadcast_misses
            miss_traffic += host.metadata_cache.broadcast_misses
            total_traffic += host.metadata_cache.broadcast_found
            found_traffic += host.metadata_cache.broadcast_found
            total_traffic += host.metadata_cache.broadcast_invalidates
            invalidate_traffic += host.metadata_cache.broadcast_invalidates

        print(f'traffic stats:\ntotal:\t{total_traffic}\noffer broadcast:\t{offer_traffic}\nmiss broadcast:\t{miss_traffic}\nremote_hit:\t{found_traffic}\ninvalidate:\t{invalidate_traffic}')
        f.write(f'traffic stats:\ntotal:\t{total_traffic}\noffer broadcast:\t{offer_traffic}\nmiss broadcast:\t{miss_traffic}\nremote_hit:\t{found_traffic}\ninvalidate:\t{invalidate_traffic}')
        f.close()

def test_cache(c):
    hits = 0
    misses = 0

    for _ in range(1000):
        a = random.randint(0, MEM_SIZE)
        if c.access(a):
            hits += 1
        else:
            misses += 1
            c.fill(a)

    print(f'Final stats dump:\nhits:\t{hits}\nmisses:\t{misses}')

def test_metadata_cache(c, data_accesses):
    import random
    import time

    start = time.time()
    for _ in range(data_accesses):
        a = random.randint(0, MEM_SIZE)
        if random.randint(0, 1) == 0:              ############################## UNCOMMENTED IF ELSE
            #c.data_read(a)
            c.data_read_write(a, True)
        else:
            #c.data_write(a)
            c.data_read_write(a, False)
        #c.data_read(a)                      ########################### COMMENTED THIS
    end = time.time()

    hit_rate = sum(c.hits) / (sum(c.hits) + sum(c.misses))
    read_hit_rate = c.num_read_hits / (c.num_read_hits + c.num_read_misses)
    write_hit_rate = c.num_write_hits / (c.num_write_hits + c.num_write_misses)   ################################## UNCOMMENTED
    #write_hit_rate = 0.
    avg_auth_path = (sum(c.hits) + sum(c.misses)) / data_accesses
    print(f'Final stats dump:\nhit rate:\t{hit_rate}\nread hit rate:\t{read_hit_rate}\nwrite hit rate:\t{write_hit_rate}\nhits:\t{c.hits}\nmisses:\t{c.misses}')

    print(f'simulator runtime:\t{end - start}')

if __name__ == '__main__':
    if sys.argv[1] == 'random':
        c = CAPULET(int(sys.argv[2]), ['random'] * int(sys.argv[2]))
        c.do_random_work()
        c.dump_stats()                                        ########################## ADDED dump_stats()
    else:
        list_trace = []
        for i in range(2, len(sys.argv)):
            if not os.path.isfile(sys.argv[i]):
                print(f"{sys.argv[i]}: File not found, terminating.")
                exit(0)
            list_trace.append(sys.argv[i])
        #c = CAPULET(int(sys.argv[1]), [sys.argv[2]] * int(sys.argv[1]))
        #c = CAPULET(int(sys.argv[1]), sys.argv[2])
        c = CAPULET(int(sys.argv[1]), list_trace)
        c.do_work()
        c.dump_stats()
