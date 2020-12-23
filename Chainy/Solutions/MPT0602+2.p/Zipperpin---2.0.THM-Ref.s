%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0602+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DYREI8Exv2

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:57 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   27 (  37 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :   86 ( 137 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_15_type,type,(
    sk_B_15: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(t206_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ ( k1_xboole_0 @ B ) )
      & ( v4_relat_1 @ ( k1_xboole_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v5_relat_1 @ ( k1_xboole_0 @ B ) )
        & ( v4_relat_1 @ ( k1_xboole_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t206_relat_1])).

thf('0',plain,
    ( ~ ( v4_relat_1 @ ( k1_xboole_0 @ sk_A_5 ) )
    | ~ ( v5_relat_1 @ ( k1_xboole_0 @ sk_B_15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v4_relat_1 @ ( k1_xboole_0 @ sk_A_5 ) )
   <= ~ ( v4_relat_1 @ ( k1_xboole_0 @ sk_A_5 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ ( k1_xboole_0 @ B ) )
      & ( v4_relat_1 @ ( k1_xboole_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X2176: $i] :
      ( v4_relat_1 @ ( k1_xboole_0 @ X2176 ) ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    ! [X2176: $i] :
      ( v4_relat_1 @ ( o_0_0_xboole_0 @ X2176 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( $false
   <= ~ ( v4_relat_1 @ ( k1_xboole_0 @ sk_A_5 ) ) ),
    inference(demod,[status(thm)],['1','2','5'])).

thf('7',plain,(
    ! [X2175: $i] :
      ( v5_relat_1 @ ( k1_xboole_0 @ X2175 ) ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    ! [X2175: $i] :
      ( v5_relat_1 @ ( o_0_0_xboole_0 @ X2175 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,
    ( ~ ( v5_relat_1 @ ( k1_xboole_0 @ sk_B_15 ) )
   <= ~ ( v5_relat_1 @ ( k1_xboole_0 @ sk_B_15 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ~ ( v5_relat_1 @ ( o_0_0_xboole_0 @ sk_B_15 ) )
   <= ~ ( v5_relat_1 @ ( k1_xboole_0 @ sk_B_15 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v5_relat_1 @ ( k1_xboole_0 @ sk_B_15 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,
    ( ~ ( v4_relat_1 @ ( k1_xboole_0 @ sk_A_5 ) )
    | ~ ( v5_relat_1 @ ( k1_xboole_0 @ sk_B_15 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,(
    ~ ( v4_relat_1 @ ( k1_xboole_0 @ sk_A_5 ) ) ),
    inference('sat_resolution*',[status(thm)],['13','14'])).

thf('16',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['6','15'])).

%------------------------------------------------------------------------------
