%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.64mInB5DWa

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:04 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 542 expanded)
%              Number of leaves         :   25 ( 195 expanded)
%              Depth                    :   16
%              Number of atoms          : 1155 (6327 expanded)
%              Number of equality atoms :   92 ( 528 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t104_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ A @ C @ B @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t104_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t99_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ A @ C ) ) )).

thf('1',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( k1_enumset1 @ X55 @ X54 @ X56 )
      = ( k1_enumset1 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t99_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('2',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 )
      = ( k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('3',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k6_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 ) @ ( k2_tarski @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 )
      = ( k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('10',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k6_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) @ ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X3 @ X2 @ X1 @ X0 @ X6 @ X6 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X6 @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t60_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k5_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 ) @ ( k2_tarski @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('22',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k5_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 )
      = ( k4_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('26',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','27'])).

thf('29',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 )
      = ( k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('31',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('35',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 ) @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('39',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( k1_enumset1 @ X55 @ X54 @ X56 )
      = ( k1_enumset1 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t99_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('44',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','42','43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 ) @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 )
      = ( k4_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X3 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','45'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('62',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 )
      = ( k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','46','59','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X3 @ X2 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','46','59','64','65'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X3 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( k1_enumset1 @ X55 @ X54 @ X56 )
      = ( k1_enumset1 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t99_enumset1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X3 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','77'])).

thf('79',plain,(
    $false ),
    inference(simplify,[status(thm)],['78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.64mInB5DWa
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:37:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.43/1.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.43/1.67  % Solved by: fo/fo7.sh
% 1.43/1.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.43/1.67  % done 1561 iterations in 1.225s
% 1.43/1.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.43/1.67  % SZS output start Refutation
% 1.43/1.67  thf(sk_A_type, type, sk_A: $i).
% 1.43/1.67  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.43/1.67  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 1.43/1.67                                           $i > $i).
% 1.43/1.67  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 1.43/1.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.43/1.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.43/1.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.43/1.67  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.43/1.67  thf(sk_C_type, type, sk_C: $i).
% 1.43/1.67  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.43/1.67  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.43/1.67  thf(sk_D_type, type, sk_D: $i).
% 1.43/1.67  thf(sk_B_type, type, sk_B: $i).
% 1.43/1.67  thf(t104_enumset1, conjecture,
% 1.43/1.67    (![A:$i,B:$i,C:$i,D:$i]:
% 1.43/1.67     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 1.43/1.67  thf(zf_stmt_0, negated_conjecture,
% 1.43/1.67    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.43/1.67        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ) )),
% 1.43/1.67    inference('cnf.neg', [status(esa)], [t104_enumset1])).
% 1.43/1.67  thf('0', plain,
% 1.43/1.67      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.43/1.67         != (k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D))),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf(t99_enumset1, axiom,
% 1.43/1.67    (![A:$i,B:$i,C:$i]:
% 1.43/1.67     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ A @ C ) ))).
% 1.43/1.67  thf('1', plain,
% 1.43/1.67      (![X54 : $i, X55 : $i, X56 : $i]:
% 1.43/1.67         ((k1_enumset1 @ X55 @ X54 @ X56) = (k1_enumset1 @ X54 @ X55 @ X56))),
% 1.43/1.67      inference('cnf', [status(esa)], [t99_enumset1])).
% 1.43/1.67  thf(t73_enumset1, axiom,
% 1.43/1.67    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.43/1.67     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.43/1.67       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.43/1.67  thf('2', plain,
% 1.43/1.67      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.43/1.67         ((k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47)
% 1.43/1.67           = (k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47))),
% 1.43/1.67      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.43/1.67  thf(t72_enumset1, axiom,
% 1.43/1.67    (![A:$i,B:$i,C:$i,D:$i]:
% 1.43/1.67     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.43/1.67  thf('3', plain,
% 1.43/1.67      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.43/1.67         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 1.43/1.67           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 1.43/1.67      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.43/1.67  thf(t71_enumset1, axiom,
% 1.43/1.67    (![A:$i,B:$i,C:$i]:
% 1.43/1.67     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.43/1.67  thf('4', plain,
% 1.43/1.67      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.43/1.67         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 1.43/1.67           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 1.43/1.67      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.43/1.67  thf('5', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.67         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['3', '4'])).
% 1.43/1.67  thf('6', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.67         ((k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0)
% 1.43/1.67           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['2', '5'])).
% 1.43/1.67  thf(t67_enumset1, axiom,
% 1.43/1.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.43/1.67     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 1.43/1.67       ( k2_xboole_0 @
% 1.43/1.67         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 1.43/1.67  thf('7', plain,
% 1.43/1.67      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, 
% 1.43/1.67         X32 : $i]:
% 1.43/1.67         ((k6_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 1.43/1.67           = (k2_xboole_0 @ 
% 1.43/1.67              (k4_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30) @ 
% 1.43/1.67              (k2_tarski @ X31 @ X32)))),
% 1.43/1.67      inference('cnf', [status(esa)], [t67_enumset1])).
% 1.43/1.67  thf('8', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.43/1.67         ((k6_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3)
% 1.43/1.67           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 1.43/1.67              (k2_tarski @ X4 @ X3)))),
% 1.43/1.67      inference('sup+', [status(thm)], ['6', '7'])).
% 1.43/1.67  thf('9', plain,
% 1.43/1.67      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.43/1.67         ((k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47)
% 1.43/1.67           = (k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47))),
% 1.43/1.67      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.43/1.67  thf('10', plain,
% 1.43/1.67      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.43/1.67         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 1.43/1.67           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 1.43/1.67      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.43/1.67  thf('11', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 1.43/1.67           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['9', '10'])).
% 1.43/1.67  thf('12', plain,
% 1.43/1.67      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.43/1.67         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 1.43/1.67           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 1.43/1.67      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.43/1.67  thf(l75_enumset1, axiom,
% 1.43/1.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.43/1.67     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 1.43/1.67       ( k2_xboole_0 @
% 1.43/1.67         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 1.43/1.67  thf('13', plain,
% 1.43/1.67      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, 
% 1.43/1.67         X11 : $i]:
% 1.43/1.67         ((k6_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11)
% 1.43/1.67           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X5 @ X6 @ X7) @ 
% 1.43/1.67              (k2_enumset1 @ X8 @ X9 @ X10 @ X11)))),
% 1.43/1.67      inference('cnf', [status(esa)], [l75_enumset1])).
% 1.43/1.67  thf('14', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.43/1.67         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0)
% 1.43/1.67           = (k2_xboole_0 @ (k2_enumset1 @ X6 @ X5 @ X4 @ X3) @ 
% 1.43/1.67              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 1.43/1.67      inference('sup+', [status(thm)], ['12', '13'])).
% 1.43/1.67  thf('15', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.43/1.67         ((k6_enumset1 @ X3 @ X2 @ X1 @ X0 @ X6 @ X6 @ X5 @ X4)
% 1.43/1.67           = (k2_xboole_0 @ (k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0) @ 
% 1.43/1.67              (k1_enumset1 @ X6 @ X5 @ X4)))),
% 1.43/1.67      inference('sup+', [status(thm)], ['11', '14'])).
% 1.43/1.67  thf('16', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X2) @ (k2_tarski @ X1 @ X0))
% 1.43/1.67           = (k2_xboole_0 @ (k4_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X3) @ 
% 1.43/1.67              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 1.43/1.67      inference('sup+', [status(thm)], ['8', '15'])).
% 1.43/1.67  thf(t69_enumset1, axiom,
% 1.43/1.67    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.43/1.67  thf('17', plain,
% 1.43/1.67      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 1.43/1.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.43/1.67  thf('18', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.67         ((k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0)
% 1.43/1.67           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['2', '5'])).
% 1.43/1.67  thf('19', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.67         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['3', '4'])).
% 1.43/1.67  thf(t60_enumset1, axiom,
% 1.43/1.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.43/1.67     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 1.43/1.67       ( k2_xboole_0 @
% 1.43/1.67         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 1.43/1.67  thf('20', plain,
% 1.43/1.67      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.43/1.67         ((k5_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24)
% 1.43/1.67           = (k2_xboole_0 @ (k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22) @ 
% 1.43/1.67              (k2_tarski @ X23 @ X24)))),
% 1.43/1.67      inference('cnf', [status(esa)], [t60_enumset1])).
% 1.43/1.67  thf('21', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.43/1.67         ((k5_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3)
% 1.43/1.67           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 1.43/1.67              (k2_tarski @ X4 @ X3)))),
% 1.43/1.67      inference('sup+', [status(thm)], ['19', '20'])).
% 1.43/1.67  thf(t74_enumset1, axiom,
% 1.43/1.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.43/1.67     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 1.43/1.67       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 1.43/1.67  thf('22', plain,
% 1.43/1.67      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 1.43/1.67         ((k5_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53)
% 1.43/1.67           = (k4_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53))),
% 1.43/1.67      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.43/1.67  thf('23', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.43/1.67         ((k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3)
% 1.43/1.67           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 1.43/1.67              (k2_tarski @ X4 @ X3)))),
% 1.43/1.67      inference('demod', [status(thm)], ['21', '22'])).
% 1.43/1.67  thf('24', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.67         ((k1_enumset1 @ X2 @ X1 @ X0)
% 1.43/1.67           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X2) @ 
% 1.43/1.67              (k2_tarski @ X1 @ X0)))),
% 1.43/1.67      inference('sup+', [status(thm)], ['18', '23'])).
% 1.43/1.67  thf(t70_enumset1, axiom,
% 1.43/1.67    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.43/1.67  thf('25', plain,
% 1.43/1.67      (![X34 : $i, X35 : $i]:
% 1.43/1.67         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 1.43/1.67      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.43/1.67  thf('26', plain,
% 1.43/1.67      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 1.43/1.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.43/1.67  thf('27', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.67         ((k1_enumset1 @ X2 @ X1 @ X0)
% 1.43/1.67           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 1.43/1.67      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.43/1.67  thf('28', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]:
% 1.43/1.67         ((k1_enumset1 @ X1 @ X0 @ X0)
% 1.43/1.67           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 1.43/1.67      inference('sup+', [status(thm)], ['17', '27'])).
% 1.43/1.67  thf('29', plain,
% 1.43/1.67      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.43/1.67         ((k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47)
% 1.43/1.67           = (k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47))),
% 1.43/1.67      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.43/1.67  thf('30', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.67         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['3', '4'])).
% 1.43/1.67  thf('31', plain,
% 1.43/1.67      (![X34 : $i, X35 : $i]:
% 1.43/1.67         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 1.43/1.67      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.43/1.67  thf('32', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]:
% 1.43/1.67         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['30', '31'])).
% 1.43/1.67  thf('33', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]:
% 1.43/1.67         ((k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['29', '32'])).
% 1.43/1.67  thf('34', plain,
% 1.43/1.67      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.43/1.67         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 1.43/1.67           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 1.43/1.67      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.43/1.67  thf(t55_enumset1, axiom,
% 1.43/1.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.43/1.67     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 1.43/1.67       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 1.43/1.67  thf('35', plain,
% 1.43/1.67      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.43/1.67         ((k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17)
% 1.43/1.67           = (k2_xboole_0 @ (k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16) @ 
% 1.43/1.67              (k1_tarski @ X17)))),
% 1.43/1.67      inference('cnf', [status(esa)], [t55_enumset1])).
% 1.43/1.67  thf('36', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.43/1.67         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 1.43/1.67           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 1.43/1.67              (k1_tarski @ X4)))),
% 1.43/1.67      inference('sup+', [status(thm)], ['34', '35'])).
% 1.43/1.67  thf('37', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]:
% 1.43/1.67         ((k2_tarski @ X1 @ X0)
% 1.43/1.67           = (k2_xboole_0 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X1) @ 
% 1.43/1.67              (k1_tarski @ X0)))),
% 1.43/1.67      inference('sup+', [status(thm)], ['33', '36'])).
% 1.43/1.67  thf('38', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.67         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['3', '4'])).
% 1.43/1.67  thf('39', plain,
% 1.43/1.67      (![X54 : $i, X55 : $i, X56 : $i]:
% 1.43/1.67         ((k1_enumset1 @ X55 @ X54 @ X56) = (k1_enumset1 @ X54 @ X55 @ X56))),
% 1.43/1.67      inference('cnf', [status(esa)], [t99_enumset1])).
% 1.43/1.67  thf('40', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.67         ((k1_enumset1 @ X1 @ X2 @ X0) = (k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['38', '39'])).
% 1.43/1.67  thf('41', plain,
% 1.43/1.67      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.43/1.67         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 1.43/1.67           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 1.43/1.67      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.43/1.67  thf('42', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.67         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X1 @ X2 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['40', '41'])).
% 1.43/1.67  thf('43', plain,
% 1.43/1.67      (![X34 : $i, X35 : $i]:
% 1.43/1.67         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 1.43/1.67      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.43/1.67  thf('44', plain,
% 1.43/1.67      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 1.43/1.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.43/1.67  thf('45', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]:
% 1.43/1.67         ((k2_tarski @ X1 @ X0)
% 1.43/1.67           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 1.43/1.67      inference('demod', [status(thm)], ['37', '42', '43', '44'])).
% 1.43/1.67  thf('46', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]:
% 1.43/1.67         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.43/1.67      inference('demod', [status(thm)], ['28', '45'])).
% 1.43/1.67  thf('47', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.67         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['3', '4'])).
% 1.43/1.67  thf('48', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 1.43/1.67           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['9', '10'])).
% 1.43/1.67  thf('49', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.43/1.67         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 1.43/1.67           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 1.43/1.67              (k1_tarski @ X4)))),
% 1.43/1.67      inference('sup+', [status(thm)], ['34', '35'])).
% 1.43/1.67  thf('50', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 1.43/1.67           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X3 @ X2 @ X1) @ 
% 1.43/1.67              (k1_tarski @ X0)))),
% 1.43/1.67      inference('sup+', [status(thm)], ['48', '49'])).
% 1.43/1.67  thf('51', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.67         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X1 @ X2 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['40', '41'])).
% 1.43/1.67  thf('52', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 1.43/1.67           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X1) @ (k1_tarski @ X0)))),
% 1.43/1.67      inference('demod', [status(thm)], ['50', '51'])).
% 1.43/1.67  thf('53', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k2_enumset1 @ X1 @ X2 @ X0 @ X3)
% 1.43/1.67           = (k2_xboole_0 @ (k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) @ 
% 1.43/1.67              (k1_tarski @ X3)))),
% 1.43/1.67      inference('sup+', [status(thm)], ['47', '52'])).
% 1.43/1.67  thf('54', plain,
% 1.43/1.67      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.43/1.67         ((k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17)
% 1.43/1.67           = (k2_xboole_0 @ (k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16) @ 
% 1.43/1.67              (k1_tarski @ X17)))),
% 1.43/1.67      inference('cnf', [status(esa)], [t55_enumset1])).
% 1.43/1.67  thf('55', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k2_enumset1 @ X1 @ X2 @ X0 @ X3)
% 1.43/1.67           = (k4_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X3))),
% 1.43/1.67      inference('demod', [status(thm)], ['53', '54'])).
% 1.43/1.67  thf('56', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.43/1.67         ((k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3)
% 1.43/1.67           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 1.43/1.67              (k2_tarski @ X4 @ X3)))),
% 1.43/1.67      inference('demod', [status(thm)], ['21', '22'])).
% 1.43/1.67  thf('57', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 1.43/1.67           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X3) @ 
% 1.43/1.67              (k2_tarski @ X1 @ X0)))),
% 1.43/1.67      inference('sup+', [status(thm)], ['55', '56'])).
% 1.43/1.67  thf('58', plain,
% 1.43/1.67      (![X34 : $i, X35 : $i]:
% 1.43/1.67         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 1.43/1.67      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.43/1.67  thf('59', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 1.43/1.67           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X1 @ X0)))),
% 1.43/1.67      inference('demod', [status(thm)], ['57', '58'])).
% 1.43/1.67  thf('60', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]:
% 1.43/1.67         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.43/1.67      inference('demod', [status(thm)], ['28', '45'])).
% 1.43/1.67  thf('61', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.67         ((k1_enumset1 @ X1 @ X2 @ X0) = (k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['38', '39'])).
% 1.43/1.67  thf('62', plain,
% 1.43/1.67      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.43/1.67         ((k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47)
% 1.43/1.67           = (k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47))),
% 1.43/1.67      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.43/1.67  thf('63', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.67         ((k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X2 @ X0)
% 1.43/1.67           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['61', '62'])).
% 1.43/1.67  thf('64', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]:
% 1.43/1.67         ((k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['60', '63'])).
% 1.43/1.67  thf('65', plain,
% 1.43/1.67      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 1.43/1.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.43/1.67  thf('66', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k2_enumset1 @ X2 @ X3 @ X1 @ X0)
% 1.43/1.67           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 1.43/1.67      inference('demod', [status(thm)], ['16', '46', '59', '64', '65'])).
% 1.43/1.67  thf('67', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k2_enumset1 @ X1 @ X3 @ X2 @ X0)
% 1.43/1.67           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 1.43/1.67      inference('sup+', [status(thm)], ['1', '66'])).
% 1.43/1.67  thf('68', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k2_enumset1 @ X2 @ X3 @ X1 @ X0)
% 1.43/1.67           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 1.43/1.67      inference('demod', [status(thm)], ['16', '46', '59', '64', '65'])).
% 1.43/1.67  thf('69', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k2_enumset1 @ X1 @ X2 @ X3 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['67', '68'])).
% 1.43/1.67  thf('70', plain,
% 1.43/1.67      (![X54 : $i, X55 : $i, X56 : $i]:
% 1.43/1.67         ((k1_enumset1 @ X55 @ X54 @ X56) = (k1_enumset1 @ X54 @ X55 @ X56))),
% 1.43/1.67      inference('cnf', [status(esa)], [t99_enumset1])).
% 1.43/1.67  thf('71', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 1.43/1.67           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X1) @ (k1_tarski @ X0)))),
% 1.43/1.67      inference('demod', [status(thm)], ['50', '51'])).
% 1.43/1.67  thf('72', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 1.43/1.67           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 1.43/1.67      inference('sup+', [status(thm)], ['70', '71'])).
% 1.43/1.67  thf('73', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 1.43/1.67           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X1) @ (k1_tarski @ X0)))),
% 1.43/1.67      inference('demod', [status(thm)], ['50', '51'])).
% 1.43/1.67  thf('74', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k2_enumset1 @ X2 @ X3 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['72', '73'])).
% 1.43/1.67  thf('75', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k2_enumset1 @ X2 @ X1 @ X3 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['69', '74'])).
% 1.43/1.67  thf('76', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k2_enumset1 @ X2 @ X3 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['72', '73'])).
% 1.43/1.67  thf('77', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((k2_enumset1 @ X3 @ X1 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['75', '76'])).
% 1.43/1.67  thf('78', plain,
% 1.43/1.67      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.43/1.67         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 1.43/1.67      inference('demod', [status(thm)], ['0', '77'])).
% 1.43/1.67  thf('79', plain, ($false), inference('simplify', [status(thm)], ['78'])).
% 1.43/1.67  
% 1.43/1.67  % SZS output end Refutation
% 1.43/1.67  
% 1.43/1.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
