
This is the tool for multibranch forging simulation for PoS crypto-currencies networks. Please read our papers around that:

* [Multibranch Forging](http://www.scribd.com/doc/248208963/Multibranch-forging)

* (more papers soon)

(All our articles & papers could be found in [special GitHub repository](https://github.com/ConsensusResearch/articles-papers))

RUN
----

1. If you use Linux you can download & run ready executable program. Download archive with executableit & config file
 with forging model parameters there https://github.com/ConsensusResearch/MultiBranch/releases/download/1.0/multibranch-1.0.tar.gz

2. If you use other operating system or don't want to run downloaded binaries, compile program from sources & run.


COMPILE
--------

To compile you need:

1. GHC haskell compiler. 
   `sudo apt-get install ghc`

2. cabal-install for external haskell packages installation
   `sudo apt-get install cabal-install`

3. ConfigFile package, which can be locally installed
   `cabal install ConfigFile`

4. Then run `compile.sh` shell-script for Linux to compile the sources

5. The executable name is `multibranch` unless another name is manually specified

CONFIGURATION
-------------

Configuration file 'multibranch.cfg' (the name is statically defined in constants.hs, after changing recompilation
is needed) consists of the following parameters:
 strTimesFileName: String. Name of the output file for times between generated blocks in one (longest) chain.
 bUseTFDepth: bool. Boolean parameter denotes whether to use nTFDepth parameter, or do the forging to as many blocks as possible (TOO SLOW). 
 nTFDepth: Integer. Parameter means the number of blocks to forge to, they are selected from the ordered list of open blocks. If it set to 
           zero - single branch forging (with forks) is simulated.
 nFixAccounts: Integer. Number of accounts in the network besides God account. Cannot be more than 15. The systemBalance (defined in Constants.hs) 
               is distributed uniformly between them.

RUN & OUTPUT
-------------

When running the program asks the number of steps (ticks) to simulate the system. Reasonable choice is 1000-2000. The calculation time depends
on the number of accounts and depth of tree forging. Program prints results of each step to the standard output. It consists of:

1. List of correspondences between account number (starting with 'H', like H1, H2 etc) and a number of block generated by it.
   This is printed for each account.

2. The Blocktree structure for the 1st account (the notation of trees is given at https://www.scribd.com/doc/248208963/Multibranch-forging )
   For each block the generator ID is printed.

3. The number of blocks in the main chain (makes sense only after rebalacing)

4. baseTarget of the last block in the main chain (can be ignored)

Rebalancing of the Blocktree to get the longest chain is performed at the end of simulation with the similar output.
The time intervals in the main chain is output to the file defined by the 'strTimesFileName' parameter ('times.data' by default) and the distribution
can be viewed by the simplot.gp script (Gnuplot package is needed to view the diagram).
The Gnuplot can be installed with
  `sudo apt-get install gnuplot gunplot-x11`

CONTACTS & Discussion
---------------------

Please contact andruiman, andruiman@gmail.com for any reasonable questions or suggestions about the program.
Also please visit our subforum @ Nxt forum : https://nxtforum.org/consensus-research/