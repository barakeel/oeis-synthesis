# run as
# shuf < sol0gpt | ./mktrain.pl

my $c=0;
open(G,">dev.miz") or die;
open(H,">dev.ferp") or die;
while(<>)
{
    $c++;
    if($c==301)
    {
        close G; close H;
        open(G,">test.miz") or die;
        open(H,">test.ferp") or die;
    }
    elsif($c==601)
    {
        close G; close H;
        open(G,">train.miz") or die;
        open(H,">train.ferp") or die;
    }
    chomp;
    s/ +/ /g;
    m/^(.*)>(.*)/ or die;
    my ($l,$r)=($1,$2);
    $l=~s/ / # /g;
    $l=~s/([_~0-9])/$1 /g;
    $l= $l . " #";
    $l=~s/ +/ /g;
    my @g = reverse split(/ /,$r);
    print G $l,"\n";
    print H join(" ",@g),"\n";
}

close G; close H;

open(G,">vocab.miz") or die;
open(H,">vocab.ferp") or die;

print G
'#
0
1
2
3
4
5
6
7
8
9
~
_
'
    ;

print H
'A
B
C
D
E
F
G
H
I
J
K
L
M
N
'
    ;

close G; close H;

