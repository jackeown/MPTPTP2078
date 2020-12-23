%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MyD0xTwi9q

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:34 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 340 expanded)
%              Number of leaves         :   33 ( 124 expanded)
%              Depth                    :   17
%              Number of atoms          : 1157 (4195 expanded)
%              Number of equality atoms :   91 ( 317 expanded)
%              Maximal formula depth    :   18 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('0',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X56 @ X57 ) ) @ ( k1_relat_1 @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('1',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X58 ) @ X59 )
      | ( ( k7_relat_1 @ X58 @ X59 )
        = X58 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X51 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X53 @ X54 ) @ X55 )
        = ( k7_relat_1 @ X53 @ ( k3_xboole_0 @ X54 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t192_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k7_relat_1 @ B @ A )
          = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t192_relat_1])).

thf('8',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('11',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k6_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 ) @ ( k2_tarski @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X6 @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('16',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k5_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 )
      = ( k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('17',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('19',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k6_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 )
      = ( k5_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) )
      = ( k3_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','28'])).

thf('30',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','28'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('39',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('43',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k5_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 ) @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X1 @ X2 @ X3 @ X4 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('57',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X3 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X1 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['38','65'])).

thf('67',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','68','69'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('71',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','74'])).

thf('76',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != ( k7_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference(simplify,[status(thm)],['78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MyD0xTwi9q
% 0.14/0.37  % Computer   : n015.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 09:17:23 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.69/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.88  % Solved by: fo/fo7.sh
% 0.69/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.88  % done 570 iterations in 0.393s
% 0.69/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.88  % SZS output start Refutation
% 0.69/0.88  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.69/0.88  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.69/0.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.69/0.88  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.69/0.88  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.69/0.88  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.69/0.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.69/0.88  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.69/0.88  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.69/0.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.69/0.88  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.69/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.88  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.69/0.88                                           $i > $i).
% 0.69/0.88  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.69/0.88  thf(t89_relat_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( v1_relat_1 @ B ) =>
% 0.69/0.88       ( r1_tarski @
% 0.69/0.88         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 0.69/0.88  thf('0', plain,
% 0.69/0.88      (![X56 : $i, X57 : $i]:
% 0.69/0.88         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X56 @ X57)) @ 
% 0.69/0.88           (k1_relat_1 @ X56))
% 0.69/0.88          | ~ (v1_relat_1 @ X56))),
% 0.69/0.88      inference('cnf', [status(esa)], [t89_relat_1])).
% 0.69/0.88  thf(t97_relat_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( v1_relat_1 @ B ) =>
% 0.69/0.88       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.69/0.88         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.69/0.88  thf('1', plain,
% 0.69/0.88      (![X58 : $i, X59 : $i]:
% 0.69/0.88         (~ (r1_tarski @ (k1_relat_1 @ X58) @ X59)
% 0.69/0.88          | ((k7_relat_1 @ X58 @ X59) = (X58))
% 0.69/0.88          | ~ (v1_relat_1 @ X58))),
% 0.69/0.88      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.69/0.88  thf('2', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.69/0.88          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.69/0.88              = (k7_relat_1 @ X0 @ X1)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['0', '1'])).
% 0.69/0.88  thf(dt_k7_relat_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.69/0.88  thf('3', plain,
% 0.69/0.88      (![X51 : $i, X52 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X51) | (v1_relat_1 @ (k7_relat_1 @ X51 @ X52)))),
% 0.69/0.88      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.69/0.88  thf('4', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.69/0.88            = (k7_relat_1 @ X0 @ X1))
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('clc', [status(thm)], ['2', '3'])).
% 0.69/0.88  thf(t100_relat_1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( v1_relat_1 @ C ) =>
% 0.69/0.88       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.69/0.88         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.69/0.88  thf('5', plain,
% 0.69/0.88      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.69/0.88         (((k7_relat_1 @ (k7_relat_1 @ X53 @ X54) @ X55)
% 0.69/0.88            = (k7_relat_1 @ X53 @ (k3_xboole_0 @ X54 @ X55)))
% 0.69/0.88          | ~ (v1_relat_1 @ X53))),
% 0.69/0.88      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.69/0.88  thf('6', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (((k7_relat_1 @ X1 @ X0)
% 0.69/0.88            = (k7_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ X1))))
% 0.69/0.88          | ~ (v1_relat_1 @ X1)
% 0.69/0.88          | ~ (v1_relat_1 @ X1))),
% 0.69/0.88      inference('sup+', [status(thm)], ['4', '5'])).
% 0.69/0.88  thf('7', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X1)
% 0.69/0.88          | ((k7_relat_1 @ X1 @ X0)
% 0.69/0.88              = (k7_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ X1)))))),
% 0.69/0.88      inference('simplify', [status(thm)], ['6'])).
% 0.69/0.88  thf(t192_relat_1, conjecture,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( v1_relat_1 @ B ) =>
% 0.69/0.88       ( ( k7_relat_1 @ B @ A ) =
% 0.69/0.88         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.69/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.88    (~( ![A:$i,B:$i]:
% 0.69/0.88        ( ( v1_relat_1 @ B ) =>
% 0.69/0.88          ( ( k7_relat_1 @ B @ A ) =
% 0.69/0.88            ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )),
% 0.69/0.88    inference('cnf.neg', [status(esa)], [t192_relat_1])).
% 0.69/0.88  thf('8', plain,
% 0.69/0.88      (((k7_relat_1 @ sk_B @ sk_A)
% 0.69/0.88         != (k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(t69_enumset1, axiom,
% 0.69/0.88    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.69/0.88  thf('9', plain, (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.69/0.88      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.69/0.88  thf(t70_enumset1, axiom,
% 0.69/0.88    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.69/0.88  thf('10', plain,
% 0.69/0.88      (![X20 : $i, X21 : $i]:
% 0.69/0.88         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.69/0.88      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.69/0.88  thf('11', plain,
% 0.69/0.88      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.69/0.88      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.69/0.88  thf('12', plain,
% 0.69/0.88      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['10', '11'])).
% 0.69/0.88  thf(t73_enumset1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.69/0.88     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.69/0.88       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.69/0.88  thf('13', plain,
% 0.69/0.88      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.69/0.88         ((k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.69/0.88           = (k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 0.69/0.88      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.69/0.88  thf(t67_enumset1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.69/0.88     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.69/0.88       ( k2_xboole_0 @
% 0.69/0.88         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 0.69/0.88  thf('14', plain,
% 0.69/0.88      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, 
% 0.69/0.88         X18 : $i]:
% 0.69/0.88         ((k6_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.69/0.88           = (k2_xboole_0 @ 
% 0.69/0.88              (k4_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16) @ 
% 0.69/0.88              (k2_tarski @ X17 @ X18)))),
% 0.69/0.88      inference('cnf', [status(esa)], [t67_enumset1])).
% 0.69/0.88  thf('15', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.69/0.88         ((k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5)
% 0.69/0.88           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.69/0.88              (k2_tarski @ X6 @ X5)))),
% 0.69/0.88      inference('sup+', [status(thm)], ['13', '14'])).
% 0.69/0.88  thf(t74_enumset1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.69/0.88     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.69/0.88       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.69/0.88  thf('16', plain,
% 0.69/0.88      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.69/0.88         ((k5_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39)
% 0.69/0.88           = (k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39))),
% 0.69/0.88      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.69/0.88  thf('17', plain,
% 0.69/0.88      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.69/0.88         ((k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.69/0.88           = (k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 0.69/0.88      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.69/0.88  thf('18', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.88         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.69/0.88           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['16', '17'])).
% 0.69/0.88  thf(t75_enumset1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.69/0.88     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.69/0.88       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.69/0.88  thf('19', plain,
% 0.69/0.88      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.69/0.88         ((k6_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46)
% 0.69/0.88           = (k5_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46))),
% 0.69/0.88      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.69/0.88  thf('20', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.88         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.69/0.88           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['18', '19'])).
% 0.69/0.88  thf('21', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.88         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2) @ 
% 0.69/0.88           (k2_tarski @ X1 @ X0)) = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['15', '20'])).
% 0.69/0.88  thf(t72_enumset1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.88     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.69/0.88  thf('22', plain,
% 0.69/0.88      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.69/0.88         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 0.69/0.88           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 0.69/0.88      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.69/0.88  thf(t71_enumset1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.69/0.88  thf('23', plain,
% 0.69/0.88      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.69/0.88         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 0.69/0.88           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 0.69/0.88      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.69/0.88  thf('24', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['22', '23'])).
% 0.69/0.88  thf('25', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.88         ((k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.69/0.88           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.69/0.88      inference('demod', [status(thm)], ['21', '24'])).
% 0.69/0.88  thf('26', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1))
% 0.69/0.88           = (k3_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1))),
% 0.69/0.88      inference('sup+', [status(thm)], ['12', '25'])).
% 0.69/0.88  thf('27', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['22', '23'])).
% 0.69/0.88  thf('28', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1))
% 0.69/0.88           = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.69/0.88      inference('demod', [status(thm)], ['26', '27'])).
% 0.69/0.88  thf('29', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.69/0.88           = (k1_enumset1 @ X1 @ X0 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['9', '28'])).
% 0.69/0.88  thf('30', plain,
% 0.69/0.88      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.69/0.88         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 0.69/0.88           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 0.69/0.88      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.69/0.88  thf(t125_enumset1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.88     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 0.69/0.88  thf('31', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.88         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.69/0.88      inference('cnf', [status(esa)], [t125_enumset1])).
% 0.69/0.88  thf('32', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         ((k2_enumset1 @ X0 @ X1 @ X2 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['30', '31'])).
% 0.69/0.88  thf('33', plain,
% 0.69/0.88      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.69/0.88         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 0.69/0.88           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 0.69/0.88      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.69/0.88  thf('34', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 0.69/0.88      inference('sup+', [status(thm)], ['32', '33'])).
% 0.69/0.88  thf('35', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.69/0.88           = (k1_enumset1 @ X0 @ X1 @ X1))),
% 0.69/0.88      inference('sup+', [status(thm)], ['29', '34'])).
% 0.69/0.88  thf('36', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.69/0.88           = (k1_enumset1 @ X1 @ X0 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['9', '28'])).
% 0.69/0.88  thf('37', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.69/0.88           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.69/0.88      inference('sup+', [status(thm)], ['35', '36'])).
% 0.69/0.88  thf('38', plain,
% 0.69/0.88      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['10', '11'])).
% 0.69/0.88  thf('39', plain,
% 0.69/0.88      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.69/0.88         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 0.69/0.88           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 0.69/0.88      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.69/0.88  thf('40', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.88         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.69/0.88      inference('cnf', [status(esa)], [t125_enumset1])).
% 0.69/0.88  thf('41', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.88         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 0.69/0.88           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['39', '40'])).
% 0.69/0.88  thf('42', plain,
% 0.69/0.88      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.69/0.88         ((k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.69/0.88           = (k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 0.69/0.88      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.69/0.88  thf(t61_enumset1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.69/0.88     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.69/0.88       ( k2_xboole_0 @
% 0.69/0.88         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 0.69/0.88  thf('43', plain,
% 0.69/0.88      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.69/0.88         ((k5_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.69/0.88           = (k2_xboole_0 @ (k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9) @ 
% 0.69/0.88              (k1_tarski @ X10)))),
% 0.69/0.88      inference('cnf', [status(esa)], [t61_enumset1])).
% 0.69/0.88  thf('44', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.69/0.88         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 0.69/0.88           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.69/0.88              (k1_tarski @ X5)))),
% 0.69/0.88      inference('sup+', [status(thm)], ['42', '43'])).
% 0.69/0.88  thf('45', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.88         ((k5_enumset1 @ X0 @ X0 @ X0 @ X1 @ X2 @ X3 @ X4)
% 0.69/0.88           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.69/0.88              (k1_tarski @ X4)))),
% 0.69/0.88      inference('sup+', [status(thm)], ['41', '44'])).
% 0.69/0.88  thf('46', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.88         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.69/0.88           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['16', '17'])).
% 0.69/0.88  thf('47', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.88         ((k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4)
% 0.69/0.88           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.69/0.88              (k1_tarski @ X4)))),
% 0.69/0.88      inference('demod', [status(thm)], ['45', '46'])).
% 0.69/0.88  thf('48', plain,
% 0.69/0.88      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.69/0.88         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 0.69/0.88           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 0.69/0.88      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.69/0.88  thf('49', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.69/0.88         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 0.69/0.88           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.69/0.88              (k1_tarski @ X5)))),
% 0.69/0.88      inference('sup+', [status(thm)], ['42', '43'])).
% 0.69/0.88  thf('50', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.88         ((k5_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.69/0.88           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.69/0.88              (k1_tarski @ X4)))),
% 0.69/0.88      inference('sup+', [status(thm)], ['48', '49'])).
% 0.69/0.88  thf('51', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.88         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.69/0.88           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['16', '17'])).
% 0.69/0.88  thf('52', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.88         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.69/0.88           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.69/0.88              (k1_tarski @ X4)))),
% 0.69/0.88      inference('demod', [status(thm)], ['50', '51'])).
% 0.69/0.88  thf('53', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.88         ((k3_enumset1 @ X1 @ X2 @ X3 @ X4 @ X0)
% 0.69/0.88           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['47', '52'])).
% 0.69/0.88  thf('54', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['22', '23'])).
% 0.69/0.88  thf('55', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         ((k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['53', '54'])).
% 0.69/0.88  thf('56', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.88         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 0.69/0.88           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['39', '40'])).
% 0.69/0.88  thf('57', plain,
% 0.69/0.88      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.69/0.88         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 0.69/0.88           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 0.69/0.88      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.69/0.88  thf('58', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.88         ((k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X3)
% 0.69/0.88           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['56', '57'])).
% 0.69/0.88  thf('59', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.69/0.88         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 0.69/0.88           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.69/0.88              (k1_tarski @ X5)))),
% 0.69/0.88      inference('sup+', [status(thm)], ['42', '43'])).
% 0.69/0.88  thf('60', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.88         ((k5_enumset1 @ X0 @ X0 @ X0 @ X1 @ X2 @ X3 @ X4)
% 0.69/0.88           = (k2_xboole_0 @ (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0) @ 
% 0.69/0.88              (k1_tarski @ X4)))),
% 0.69/0.88      inference('sup+', [status(thm)], ['58', '59'])).
% 0.69/0.88  thf('61', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.88         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.69/0.88           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['16', '17'])).
% 0.69/0.88  thf('62', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.88         ((k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4)
% 0.69/0.88           = (k2_xboole_0 @ (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0) @ 
% 0.69/0.88              (k1_tarski @ X4)))),
% 0.69/0.88      inference('demod', [status(thm)], ['60', '61'])).
% 0.69/0.88  thf('63', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         ((k3_enumset1 @ X0 @ X1 @ X1 @ X1 @ X2)
% 0.69/0.88           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.69/0.88      inference('sup+', [status(thm)], ['55', '62'])).
% 0.69/0.88  thf('64', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         ((k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['53', '54'])).
% 0.69/0.88  thf('65', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         ((k1_enumset1 @ X1 @ X0 @ X2)
% 0.69/0.88           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.69/0.88      inference('demod', [status(thm)], ['63', '64'])).
% 0.69/0.88  thf('66', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.69/0.88           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.69/0.88      inference('sup+', [status(thm)], ['38', '65'])).
% 0.69/0.88  thf('67', plain,
% 0.69/0.88      (![X20 : $i, X21 : $i]:
% 0.69/0.88         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.69/0.88      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.69/0.88  thf('68', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.69/0.88           = (k2_tarski @ X1 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['66', '67'])).
% 0.69/0.88  thf('69', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.69/0.88           = (k2_tarski @ X1 @ X0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['66', '67'])).
% 0.69/0.88  thf('70', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.69/0.88      inference('demod', [status(thm)], ['37', '68', '69'])).
% 0.69/0.88  thf(t12_setfam_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.69/0.88  thf('71', plain,
% 0.69/0.88      (![X49 : $i, X50 : $i]:
% 0.69/0.88         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 0.69/0.88      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.69/0.88  thf('72', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.69/0.88      inference('sup+', [status(thm)], ['70', '71'])).
% 0.69/0.88  thf('73', plain,
% 0.69/0.88      (![X49 : $i, X50 : $i]:
% 0.69/0.88         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 0.69/0.88      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.69/0.88  thf('74', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.69/0.88      inference('sup+', [status(thm)], ['72', '73'])).
% 0.69/0.88  thf('75', plain,
% 0.69/0.88      (((k7_relat_1 @ sk_B @ sk_A)
% 0.69/0.88         != (k7_relat_1 @ sk_B @ (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.69/0.88      inference('demod', [status(thm)], ['8', '74'])).
% 0.69/0.88  thf('76', plain,
% 0.69/0.88      ((((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))
% 0.69/0.88        | ~ (v1_relat_1 @ sk_B))),
% 0.69/0.88      inference('sup-', [status(thm)], ['7', '75'])).
% 0.69/0.88  thf('77', plain, ((v1_relat_1 @ sk_B)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('78', plain,
% 0.69/0.88      (((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))),
% 0.69/0.88      inference('demod', [status(thm)], ['76', '77'])).
% 0.69/0.88  thf('79', plain, ($false), inference('simplify', [status(thm)], ['78'])).
% 0.69/0.88  
% 0.69/0.88  % SZS output end Refutation
% 0.69/0.88  
% 0.69/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
