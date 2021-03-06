VAGRANTFILE_API_VERSION = "2"

Vagrant.configure(VAGRANTFILE_API_VERSION) do |config|
  config.vm.box = "ubuntu/xenial64"

  config.vm.post_up_message = <<-MSG
Welcome to Haskell backend of ABS language.

1) Compiling an ABS program to Haskell:

habs File1.abs File2.abs
# creates under gen/haskell/ the Haskell files: File1.hs, File2.hs

2) Compiling the resulting Haskell program to native code:

ghc --make -O gen/haskell/File1.hs gen/haskell/File2.hs -main-is File2
# creates a File2 executable with its entry point being the ABS main block of File2

3) Running the final ABS-program executable:

./File2 # runs the program
MSG

  config.vm.provider "virtualbox" do |vb|
    vb.memory = 4096
    vb.cpus = 2
    vb.name = "habs_vagrant"
    vb.customize ["modifyvm", :id, "--natdnshostresolver1", "on"] # fix for ubuntu DNS problems
  end

  # Install necessary software
  config.vm.provision "shell",
                      privileged: false,
                      inline: <<-SHELL

# Set up paths
cat >~/.abstoolsrc <<EOF
PATH=\$PATH:/opt/ghc/8.2.2/bin:/opt/cabal/2.0/bin:/opt/happy/1.19.5/bin:~/habs/.cabal-sandbox/bin
export GHC_PACKAGE_PATH=~/habs/.cabal-sandbox/x86_64-linux-ghc-8.2.2-packages.conf.d:
EOF

if [ -z "$(grep abstoolsrc ~/.bashrc)" ] ; then
cat >>~/.bashrc <<EOF
. .abstoolsrc
EOF
fi

echo
echo "Installing prerequisites"
echo

sudo add-apt-repository ppa:hvr/ghc
sudo apt-get update -y -q
sudo apt-get install -y -q ghc-8.2.2 cabal-install-2.0 happy-1.19.5 git zlib1g-dev

# clone habs repo and subrepos
rm -rf ~/habs
git clone https://github.com/abstools/habs ~/habs
cd ~/habs
git submodule update --init

# build habs parser + transcompiler + runtime + stdlib and all of their dependencies
export PATH=$PATH:/opt/ghc/8.2.2/bin:/opt/cabal/2.0/bin:/opt/happy/1.19.5/bin # needed to find haskell tools
unset GHC_PACKAGE_PATH # otherwise cabal will complain
cabal sandbox init
cabal update
cabal sandbox add-source habs-parser
cabal sandbox add-source habs-runtime
cabal sandbox add-source haskell-src-exts-qq
cabal install -j1 habs-runtime -fwait-all-cogs  # explicitly installing runtime to pass wait-all-cogs compile flag
cabal install -j1 # install the transcompiler (will also install parser, stdlib)


  SHELL
end
