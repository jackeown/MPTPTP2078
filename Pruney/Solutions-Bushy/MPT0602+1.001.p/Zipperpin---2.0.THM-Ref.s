%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0602+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.us7fNd2kok

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:10 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   18 (  25 expanded)
%              Number of leaves         :    7 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 ( 101 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t206_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v5_relat_1 @ k1_xboole_0 @ B )
        & ( v4_relat_1 @ k1_xboole_0 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t206_relat_1])).

thf('0',plain,
    ( ~ ( v4_relat_1 @ k1_xboole_0 @ sk_A )
    | ~ ( v5_relat_1 @ k1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v4_relat_1 @ k1_xboole_0 @ sk_A )
   <= ~ ( v4_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('2',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf('3',plain,
    ( $false
   <= ~ ( v4_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf('5',plain,
    ( ~ ( v5_relat_1 @ k1_xboole_0 @ sk_B )
   <= ~ ( v5_relat_1 @ k1_xboole_0 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,(
    v5_relat_1 @ k1_xboole_0 @ sk_B ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v4_relat_1 @ k1_xboole_0 @ sk_A )
    | ~ ( v5_relat_1 @ k1_xboole_0 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,(
    ~ ( v4_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['6','7'])).

thf('9',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['3','8'])).


%------------------------------------------------------------------------------
