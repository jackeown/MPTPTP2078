%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AMrZAQENkH

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:39 EST 2020

% Result     : Theorem 13.33s
% Output     : Refutation 13.33s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 514 expanded)
%              Number of leaves         :   25 ( 184 expanded)
%              Depth                    :   16
%              Number of atoms          : 2108 (6250 expanded)
%              Number of equality atoms :  171 ( 501 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t137_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t137_enumset1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X6 @ X4 @ X5 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X6 @ X4 @ X5 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('3',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X6 @ X4 @ X5 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X1 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X8 @ X7 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X6 @ X4 @ X5 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('18',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 ) @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('21',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X0 @ X1 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X3 )
      = ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X1 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','26'])).

thf('28',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('29',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X1 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','36'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('38',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k6_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 )
      = ( k5_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('39',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k5_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k4_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('42',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k6_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) @ ( k2_tarski @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X6 @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X1 @ X0 @ X1 @ X1 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['37','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X3 )
      = ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('50',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('51',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) )
      = ( k2_enumset1 @ X0 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X0 @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X0 @ X0 )
      = ( k2_enumset1 @ X0 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X0 @ X1 @ X0 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X8 @ X7 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('62',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X6 @ X4 @ X5 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['65','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 )
      = ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X2 )
      = ( k3_enumset1 @ X0 @ X1 @ X0 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['60','73','74'])).

thf('76',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 ) @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X1 @ X2 @ X1 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X1 @ X2 @ X1 @ X1 @ X0 @ X3 )
      = ( k3_enumset1 @ X2 @ X1 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('81',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X6 @ X4 @ X5 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('82',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X1 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('91',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X1 @ X2 )
      = ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['94','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k3_enumset1 @ X2 @ X1 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X1 @ X2 @ X1 @ X1 @ X0 @ X3 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['79','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['47','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('106',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('112',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('116',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X1 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['114','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X1 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('120',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('121',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X6 @ X4 @ X5 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X3 )
      = ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X1 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['119','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X1 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['129','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X2 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X1 @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['118','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X1 @ X2 )
      = ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X3 )
      = ( k3_enumset1 @ X2 @ X1 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['145','150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X1 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['142','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('155',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( k1_enumset1 @ X56 @ X58 @ X57 )
      = ( k1_enumset1 @ X56 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('156',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['3','104','113','153','154','155'])).

thf('157',plain,(
    $false ),
    inference(simplify,[status(thm)],['156'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AMrZAQENkH
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:18:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 13.33/13.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 13.33/13.52  % Solved by: fo/fo7.sh
% 13.33/13.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.33/13.52  % done 15078 iterations in 13.056s
% 13.33/13.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 13.33/13.52  % SZS output start Refutation
% 13.33/13.52  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 13.33/13.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 13.33/13.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 13.33/13.52  thf(sk_A_type, type, sk_A: $i).
% 13.33/13.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 13.33/13.52  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 13.33/13.52  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 13.33/13.52                                           $i > $i).
% 13.33/13.52  thf(sk_C_type, type, sk_C: $i).
% 13.33/13.52  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 13.33/13.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 13.33/13.52  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 13.33/13.52  thf(sk_B_type, type, sk_B: $i).
% 13.33/13.52  thf(t137_enumset1, conjecture,
% 13.33/13.52    (![A:$i,B:$i,C:$i]:
% 13.33/13.52     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 13.33/13.52       ( k1_enumset1 @ A @ B @ C ) ))).
% 13.33/13.52  thf(zf_stmt_0, negated_conjecture,
% 13.33/13.52    (~( ![A:$i,B:$i,C:$i]:
% 13.33/13.52        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 13.33/13.52          ( k1_enumset1 @ A @ B @ C ) ) )),
% 13.33/13.52    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 13.33/13.52  thf('0', plain,
% 13.33/13.52      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 13.33/13.52         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 13.33/13.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.33/13.52  thf(t100_enumset1, axiom,
% 13.33/13.52    (![A:$i,B:$i,C:$i]:
% 13.33/13.52     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 13.33/13.52  thf('1', plain,
% 13.33/13.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X6 @ X4 @ X5) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 13.33/13.52      inference('cnf', [status(esa)], [t100_enumset1])).
% 13.33/13.52  thf('2', plain,
% 13.33/13.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X6 @ X4 @ X5) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 13.33/13.52      inference('cnf', [status(esa)], [t100_enumset1])).
% 13.33/13.52  thf('3', plain,
% 13.33/13.52      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 13.33/13.52         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 13.33/13.52      inference('demod', [status(thm)], ['0', '1', '2'])).
% 13.33/13.52  thf(t71_enumset1, axiom,
% 13.33/13.52    (![A:$i,B:$i,C:$i]:
% 13.33/13.52     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 13.33/13.52  thf('4', plain,
% 13.33/13.52      (![X31 : $i, X32 : $i, X33 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 13.33/13.52           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 13.33/13.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 13.33/13.52  thf('5', plain,
% 13.33/13.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X6 @ X4 @ X5) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 13.33/13.52      inference('cnf', [status(esa)], [t100_enumset1])).
% 13.33/13.52  thf(t70_enumset1, axiom,
% 13.33/13.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 13.33/13.52  thf('6', plain,
% 13.33/13.52      (![X29 : $i, X30 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 13.33/13.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 13.33/13.52  thf('7', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 13.33/13.52      inference('sup+', [status(thm)], ['5', '6'])).
% 13.33/13.52  thf('8', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X0 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 13.33/13.52      inference('sup+', [status(thm)], ['4', '7'])).
% 13.33/13.52  thf(t47_enumset1, axiom,
% 13.33/13.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 13.33/13.52     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 13.33/13.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 13.33/13.52  thf('9', plain,
% 13.33/13.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14)
% 13.33/13.52           = (k2_xboole_0 @ (k1_tarski @ X10) @ 
% 13.33/13.52              (k2_enumset1 @ X11 @ X12 @ X13 @ X14)))),
% 13.33/13.52      inference('cnf', [status(esa)], [t47_enumset1])).
% 13.33/13.52  thf('10', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X2 @ X1 @ X1 @ X0 @ X1)
% 13.33/13.52           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['8', '9'])).
% 13.33/13.52  thf('11', plain,
% 13.33/13.52      (![X31 : $i, X32 : $i, X33 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 13.33/13.52           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 13.33/13.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 13.33/13.52  thf(t102_enumset1, axiom,
% 13.33/13.52    (![A:$i,B:$i,C:$i]:
% 13.33/13.52     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 13.33/13.52  thf('12', plain,
% 13.33/13.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X9 @ X8 @ X7) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 13.33/13.52      inference('cnf', [status(esa)], [t102_enumset1])).
% 13.33/13.52  thf('13', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['11', '12'])).
% 13.33/13.52  thf('14', plain,
% 13.33/13.52      (![X31 : $i, X32 : $i, X33 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 13.33/13.52           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 13.33/13.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 13.33/13.52  thf('15', plain,
% 13.33/13.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X6 @ X4 @ X5) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 13.33/13.52      inference('cnf', [status(esa)], [t100_enumset1])).
% 13.33/13.52  thf('16', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 13.33/13.52      inference('sup+', [status(thm)], ['14', '15'])).
% 13.33/13.52  thf('17', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X2 @ X2 @ X0 @ X1) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['13', '16'])).
% 13.33/13.52  thf(t72_enumset1, axiom,
% 13.33/13.52    (![A:$i,B:$i,C:$i,D:$i]:
% 13.33/13.52     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 13.33/13.52  thf('18', plain,
% 13.33/13.52      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 13.33/13.52           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 13.33/13.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 13.33/13.52  thf(t55_enumset1, axiom,
% 13.33/13.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 13.33/13.52     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 13.33/13.52       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 13.33/13.52  thf('19', plain,
% 13.33/13.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 13.33/13.52         ((k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 13.33/13.52           = (k2_xboole_0 @ (k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19) @ 
% 13.33/13.52              (k1_tarski @ X20)))),
% 13.33/13.52      inference('cnf', [status(esa)], [t55_enumset1])).
% 13.33/13.52  thf('20', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['18', '19'])).
% 13.33/13.52  thf(t73_enumset1, axiom,
% 13.33/13.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 13.33/13.52     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 13.33/13.52       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 13.33/13.52  thf('21', plain,
% 13.33/13.52      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 13.33/13.52         ((k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42)
% 13.33/13.52           = (k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 13.33/13.52      inference('cnf', [status(esa)], [t73_enumset1])).
% 13.33/13.52  thf('22', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('demod', [status(thm)], ['20', '21'])).
% 13.33/13.52  thf('23', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X2 @ X2 @ X0 @ X1 @ X3)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X3)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['17', '22'])).
% 13.33/13.52  thf('24', plain,
% 13.33/13.52      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 13.33/13.52           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 13.33/13.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 13.33/13.52  thf('25', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('demod', [status(thm)], ['20', '21'])).
% 13.33/13.52  thf('26', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X2 @ X0 @ X1 @ X3)
% 13.33/13.52           = (k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3))),
% 13.33/13.52      inference('demod', [status(thm)], ['23', '24', '25'])).
% 13.33/13.52  thf('27', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X1 @ X0 @ X1 @ X1)
% 13.33/13.52           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['10', '26'])).
% 13.33/13.52  thf('28', plain,
% 13.33/13.52      (![X31 : $i, X32 : $i, X33 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 13.33/13.52           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 13.33/13.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 13.33/13.52  thf('29', plain,
% 13.33/13.52      (![X29 : $i, X30 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 13.33/13.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 13.33/13.52  thf('30', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['28', '29'])).
% 13.33/13.52  thf('31', plain,
% 13.33/13.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14)
% 13.33/13.52           = (k2_xboole_0 @ (k1_tarski @ X10) @ 
% 13.33/13.52              (k2_enumset1 @ X11 @ X12 @ X13 @ X14)))),
% 13.33/13.52      inference('cnf', [status(esa)], [t47_enumset1])).
% 13.33/13.52  thf('32', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0)
% 13.33/13.52           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['30', '31'])).
% 13.33/13.52  thf('33', plain,
% 13.33/13.52      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 13.33/13.52           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 13.33/13.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 13.33/13.52  thf('34', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i]:
% 13.33/13.52         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 13.33/13.52           = (k2_enumset1 @ X1 @ X1 @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['32', '33'])).
% 13.33/13.52  thf('35', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['28', '29'])).
% 13.33/13.52  thf('36', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i]:
% 13.33/13.52         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 13.33/13.52           = (k2_tarski @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['34', '35'])).
% 13.33/13.52  thf('37', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X1 @ X0 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 13.33/13.52      inference('demod', [status(thm)], ['27', '36'])).
% 13.33/13.52  thf(t75_enumset1, axiom,
% 13.33/13.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 13.33/13.52     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 13.33/13.52       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 13.33/13.52  thf('38', plain,
% 13.33/13.52      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 13.33/13.52         ((k6_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55)
% 13.33/13.52           = (k5_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55))),
% 13.33/13.52      inference('cnf', [status(esa)], [t75_enumset1])).
% 13.33/13.52  thf(t74_enumset1, axiom,
% 13.33/13.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 13.33/13.52     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 13.33/13.52       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 13.33/13.52  thf('39', plain,
% 13.33/13.52      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 13.33/13.52         ((k5_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48)
% 13.33/13.52           = (k4_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48))),
% 13.33/13.52      inference('cnf', [status(esa)], [t74_enumset1])).
% 13.33/13.52  thf('40', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 13.33/13.52         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 13.33/13.52           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['38', '39'])).
% 13.33/13.52  thf('41', plain,
% 13.33/13.52      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 13.33/13.52         ((k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42)
% 13.33/13.52           = (k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 13.33/13.52      inference('cnf', [status(esa)], [t73_enumset1])).
% 13.33/13.52  thf(t67_enumset1, axiom,
% 13.33/13.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 13.33/13.52     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 13.33/13.52       ( k2_xboole_0 @
% 13.33/13.52         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 13.33/13.52  thf('42', plain,
% 13.33/13.52      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, 
% 13.33/13.52         X28 : $i]:
% 13.33/13.52         ((k6_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 13.33/13.52           = (k2_xboole_0 @ 
% 13.33/13.52              (k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26) @ 
% 13.33/13.52              (k2_tarski @ X27 @ X28)))),
% 13.33/13.52      inference('cnf', [status(esa)], [t67_enumset1])).
% 13.33/13.52  thf('43', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 13.33/13.52         ((k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5)
% 13.33/13.52           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k2_tarski @ X6 @ X5)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['41', '42'])).
% 13.33/13.52  thf('44', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 13.33/13.52         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 13.33/13.52           = (k2_xboole_0 @ (k3_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2) @ 
% 13.33/13.52              (k2_tarski @ X1 @ X0)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['40', '43'])).
% 13.33/13.52  thf('45', plain,
% 13.33/13.52      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 13.33/13.52           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 13.33/13.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 13.33/13.52  thf('46', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 13.33/13.52         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 13.33/13.52              (k2_tarski @ X1 @ X0)))),
% 13.33/13.52      inference('demod', [status(thm)], ['44', '45'])).
% 13.33/13.52  thf('47', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k4_enumset1 @ X1 @ X0 @ X1 @ X1 @ X3 @ X2)
% 13.33/13.52           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['37', '46'])).
% 13.33/13.52  thf('48', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X2 @ X0 @ X1 @ X3)
% 13.33/13.52           = (k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3))),
% 13.33/13.52      inference('demod', [status(thm)], ['23', '24', '25'])).
% 13.33/13.52  thf('49', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['11', '12'])).
% 13.33/13.52  thf('50', plain,
% 13.33/13.52      (![X31 : $i, X32 : $i, X33 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 13.33/13.52           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 13.33/13.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 13.33/13.52  thf('51', plain,
% 13.33/13.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14)
% 13.33/13.52           = (k2_xboole_0 @ (k1_tarski @ X10) @ 
% 13.33/13.52              (k2_enumset1 @ X11 @ X12 @ X13 @ X14)))),
% 13.33/13.52      inference('cnf', [status(esa)], [t47_enumset1])).
% 13.33/13.52  thf('52', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0)
% 13.33/13.52           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['50', '51'])).
% 13.33/13.52  thf('53', plain,
% 13.33/13.52      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 13.33/13.52           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 13.33/13.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 13.33/13.52  thf('54', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 13.33/13.52           = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['52', '53'])).
% 13.33/13.52  thf('55', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 13.33/13.52           = (k2_enumset1 @ X0 @ X0 @ X1 @ X2))),
% 13.33/13.52      inference('sup+', [status(thm)], ['49', '54'])).
% 13.33/13.52  thf('56', plain,
% 13.33/13.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14)
% 13.33/13.52           = (k2_xboole_0 @ (k1_tarski @ X10) @ 
% 13.33/13.52              (k2_enumset1 @ X11 @ X12 @ X13 @ X14)))),
% 13.33/13.52      inference('cnf', [status(esa)], [t47_enumset1])).
% 13.33/13.52  thf('57', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X0 @ X2 @ X2 @ X1 @ X0)
% 13.33/13.52           = (k2_enumset1 @ X0 @ X0 @ X1 @ X2))),
% 13.33/13.52      inference('demod', [status(thm)], ['55', '56'])).
% 13.33/13.52  thf('58', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X0 @ X1 @ X0 @ X0) = (k2_enumset1 @ X0 @ X0 @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['48', '57'])).
% 13.33/13.52  thf('59', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('demod', [status(thm)], ['20', '21'])).
% 13.33/13.52  thf('60', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X0 @ X0 @ X1 @ X0 @ X2)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X0 @ X1 @ X0 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X2)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['58', '59'])).
% 13.33/13.52  thf('61', plain,
% 13.33/13.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X9 @ X8 @ X7) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 13.33/13.52      inference('cnf', [status(esa)], [t102_enumset1])).
% 13.33/13.52  thf('62', plain,
% 13.33/13.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X6 @ X4 @ X5) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 13.33/13.52      inference('cnf', [status(esa)], [t100_enumset1])).
% 13.33/13.52  thf('63', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['61', '62'])).
% 13.33/13.52  thf('64', plain,
% 13.33/13.52      (![X31 : $i, X32 : $i, X33 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 13.33/13.52           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 13.33/13.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 13.33/13.52  thf('65', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['63', '64'])).
% 13.33/13.52  thf('66', plain,
% 13.33/13.52      (![X31 : $i, X32 : $i, X33 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 13.33/13.52           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 13.33/13.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 13.33/13.52  thf('67', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('demod', [status(thm)], ['20', '21'])).
% 13.33/13.52  thf('68', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 13.33/13.52           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['66', '67'])).
% 13.33/13.52  thf('69', plain,
% 13.33/13.52      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 13.33/13.52           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 13.33/13.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 13.33/13.52  thf('70', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 13.33/13.52           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 13.33/13.52      inference('demod', [status(thm)], ['68', '69'])).
% 13.33/13.52  thf('71', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X1 @ X2 @ X0 @ X3)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X3)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['65', '70'])).
% 13.33/13.52  thf('72', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('demod', [status(thm)], ['20', '21'])).
% 13.33/13.52  thf('73', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X1 @ X2 @ X0 @ X3)
% 13.33/13.52           = (k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3))),
% 13.33/13.52      inference('demod', [status(thm)], ['71', '72'])).
% 13.33/13.52  thf('74', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('demod', [status(thm)], ['20', '21'])).
% 13.33/13.52  thf('75', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X1 @ X0 @ X0 @ X2)
% 13.33/13.52           = (k3_enumset1 @ X0 @ X1 @ X0 @ X0 @ X2))),
% 13.33/13.52      inference('demod', [status(thm)], ['60', '73', '74'])).
% 13.33/13.52  thf('76', plain,
% 13.33/13.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 13.33/13.52         ((k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 13.33/13.52           = (k2_xboole_0 @ (k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19) @ 
% 13.33/13.52              (k1_tarski @ X20)))),
% 13.33/13.52      inference('cnf', [status(esa)], [t55_enumset1])).
% 13.33/13.52  thf('77', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k4_enumset1 @ X1 @ X2 @ X1 @ X1 @ X0 @ X3)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X1 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X3)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['75', '76'])).
% 13.33/13.52  thf('78', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('demod', [status(thm)], ['20', '21'])).
% 13.33/13.52  thf('79', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k4_enumset1 @ X1 @ X2 @ X1 @ X1 @ X0 @ X3)
% 13.33/13.52           = (k3_enumset1 @ X2 @ X1 @ X1 @ X0 @ X3))),
% 13.33/13.52      inference('demod', [status(thm)], ['77', '78'])).
% 13.33/13.52  thf('80', plain,
% 13.33/13.52      (![X31 : $i, X32 : $i, X33 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 13.33/13.52           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 13.33/13.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 13.33/13.52  thf('81', plain,
% 13.33/13.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X6 @ X4 @ X5) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 13.33/13.52      inference('cnf', [status(esa)], [t100_enumset1])).
% 13.33/13.52  thf('82', plain,
% 13.33/13.52      (![X29 : $i, X30 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 13.33/13.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 13.33/13.52  thf('83', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 13.33/13.52      inference('sup+', [status(thm)], ['81', '82'])).
% 13.33/13.52  thf('84', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 13.33/13.52      inference('sup+', [status(thm)], ['80', '83'])).
% 13.33/13.52  thf('85', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['28', '29'])).
% 13.33/13.52  thf('86', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1) = (k2_enumset1 @ X1 @ X1 @ X0 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['84', '85'])).
% 13.33/13.52  thf('87', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('demod', [status(thm)], ['20', '21'])).
% 13.33/13.52  thf('88', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X0 @ X0 @ X1 @ X1 @ X2)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X2)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['86', '87'])).
% 13.33/13.52  thf('89', plain,
% 13.33/13.52      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 13.33/13.52           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 13.33/13.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 13.33/13.52  thf('90', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('demod', [status(thm)], ['20', '21'])).
% 13.33/13.52  thf('91', plain,
% 13.33/13.52      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 13.33/13.52           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 13.33/13.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 13.33/13.52  thf('92', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X0 @ X1 @ X1 @ X2) = (k2_enumset1 @ X1 @ X1 @ X0 @ X2))),
% 13.33/13.52      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 13.33/13.52  thf('93', plain,
% 13.33/13.52      (![X31 : $i, X32 : $i, X33 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 13.33/13.52           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 13.33/13.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 13.33/13.52  thf('94', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['92', '93'])).
% 13.33/13.52  thf('95', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['63', '64'])).
% 13.33/13.52  thf('96', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('demod', [status(thm)], ['20', '21'])).
% 13.33/13.52  thf('97', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X1 @ X1 @ X2 @ X0 @ X3)
% 13.33/13.52           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['95', '96'])).
% 13.33/13.52  thf('98', plain,
% 13.33/13.52      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 13.33/13.52           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 13.33/13.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 13.33/13.52  thf('99', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X1 @ X2 @ X0 @ X3)
% 13.33/13.52           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 13.33/13.52      inference('demod', [status(thm)], ['97', '98'])).
% 13.33/13.52  thf('100', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X1 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X3)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['94', '99'])).
% 13.33/13.52  thf('101', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('demod', [status(thm)], ['20', '21'])).
% 13.33/13.52  thf('102', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 13.33/13.52           = (k3_enumset1 @ X2 @ X1 @ X1 @ X0 @ X3))),
% 13.33/13.52      inference('demod', [status(thm)], ['100', '101'])).
% 13.33/13.52  thf('103', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k4_enumset1 @ X1 @ X2 @ X1 @ X1 @ X0 @ X3)
% 13.33/13.52           = (k2_enumset1 @ X2 @ X1 @ X0 @ X3))),
% 13.33/13.52      inference('demod', [status(thm)], ['79', '102'])).
% 13.33/13.52  thf('104', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2)
% 13.33/13.52           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 13.33/13.52      inference('demod', [status(thm)], ['47', '103'])).
% 13.33/13.52  thf('105', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['11', '12'])).
% 13.33/13.52  thf('106', plain,
% 13.33/13.52      (![X31 : $i, X32 : $i, X33 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 13.33/13.52           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 13.33/13.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 13.33/13.52  thf('107', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X0 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['105', '106'])).
% 13.33/13.52  thf('108', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('demod', [status(thm)], ['20', '21'])).
% 13.33/13.52  thf('109', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X3)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X3)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['107', '108'])).
% 13.33/13.52  thf('110', plain,
% 13.33/13.52      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 13.33/13.52           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 13.33/13.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 13.33/13.52  thf('111', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('demod', [status(thm)], ['20', '21'])).
% 13.33/13.52  thf('112', plain,
% 13.33/13.52      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 13.33/13.52           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 13.33/13.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 13.33/13.52  thf('113', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3) = (k2_enumset1 @ X2 @ X1 @ X0 @ X3))),
% 13.33/13.52      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 13.33/13.52  thf('114', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 13.33/13.52      inference('sup+', [status(thm)], ['81', '82'])).
% 13.33/13.52  thf('115', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 13.33/13.52      inference('sup+', [status(thm)], ['14', '15'])).
% 13.33/13.52  thf('116', plain,
% 13.33/13.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14)
% 13.33/13.52           = (k2_xboole_0 @ (k1_tarski @ X10) @ 
% 13.33/13.52              (k2_enumset1 @ X11 @ X12 @ X13 @ X14)))),
% 13.33/13.52      inference('cnf', [status(esa)], [t47_enumset1])).
% 13.33/13.52  thf('117', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X0 @ X0 @ X2 @ X1)
% 13.33/13.52           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['115', '116'])).
% 13.33/13.52  thf('118', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X2 @ X1 @ X1 @ X0 @ X1)
% 13.33/13.52           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['114', '117'])).
% 13.33/13.52  thf('119', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X2 @ X1 @ X1 @ X0 @ X1)
% 13.33/13.52           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['8', '9'])).
% 13.33/13.52  thf('120', plain,
% 13.33/13.52      (![X31 : $i, X32 : $i, X33 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 13.33/13.52           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 13.33/13.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 13.33/13.52  thf('121', plain,
% 13.33/13.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X6 @ X4 @ X5) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 13.33/13.52      inference('cnf', [status(esa)], [t100_enumset1])).
% 13.33/13.52  thf('122', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X0 @ X2 @ X1) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['120', '121'])).
% 13.33/13.52  thf('123', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 13.33/13.52           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 13.33/13.52      inference('demod', [status(thm)], ['68', '69'])).
% 13.33/13.52  thf('124', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X0 @ X2 @ X1 @ X3)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X3)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['122', '123'])).
% 13.33/13.52  thf('125', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('demod', [status(thm)], ['20', '21'])).
% 13.33/13.52  thf('126', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X0 @ X2 @ X1 @ X3)
% 13.33/13.52           = (k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3))),
% 13.33/13.52      inference('demod', [status(thm)], ['124', '125'])).
% 13.33/13.52  thf('127', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X0 @ X1 @ X1 @ X1)
% 13.33/13.52           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['119', '126'])).
% 13.33/13.52  thf('128', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i]:
% 13.33/13.52         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 13.33/13.52           = (k2_tarski @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['34', '35'])).
% 13.33/13.52  thf('129', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X0 @ X1 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 13.33/13.52      inference('demod', [status(thm)], ['127', '128'])).
% 13.33/13.52  thf('130', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['28', '29'])).
% 13.33/13.52  thf('131', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('demod', [status(thm)], ['20', '21'])).
% 13.33/13.52  thf('132', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 13.33/13.52           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['130', '131'])).
% 13.33/13.52  thf('133', plain,
% 13.33/13.52      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 13.33/13.52           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 13.33/13.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 13.33/13.52  thf('134', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 13.33/13.52           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 13.33/13.52      inference('demod', [status(thm)], ['132', '133'])).
% 13.33/13.52  thf('135', plain,
% 13.33/13.52      (![X31 : $i, X32 : $i, X33 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 13.33/13.52           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 13.33/13.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 13.33/13.52  thf('136', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 13.33/13.52           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['134', '135'])).
% 13.33/13.52  thf('137', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k2_xboole_0 @ (k2_enumset1 @ X1 @ X0 @ X0 @ X0) @ (k1_tarski @ X2))
% 13.33/13.52           = (k1_enumset1 @ X0 @ X1 @ X2))),
% 13.33/13.52      inference('sup+', [status(thm)], ['129', '136'])).
% 13.33/13.52  thf('138', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('demod', [status(thm)], ['20', '21'])).
% 13.33/13.52  thf('139', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X2) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 13.33/13.52      inference('demod', [status(thm)], ['137', '138'])).
% 13.33/13.52  thf('140', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0)
% 13.33/13.52           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['30', '31'])).
% 13.33/13.52  thf('141', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X2 @ X1 @ X0)
% 13.33/13.52           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X2 @ X0)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['139', '140'])).
% 13.33/13.52  thf('142', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X2 @ X1 @ X1 @ X0 @ X1) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 13.33/13.52      inference('demod', [status(thm)], ['118', '141'])).
% 13.33/13.52  thf('143', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X0 @ X1 @ X1 @ X2) = (k2_enumset1 @ X1 @ X1 @ X0 @ X2))),
% 13.33/13.52      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 13.33/13.52  thf('144', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('demod', [status(thm)], ['20', '21'])).
% 13.33/13.52  thf('145', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X1 @ X1 @ X2 @ X0 @ X3)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X1 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X3)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['143', '144'])).
% 13.33/13.52  thf('146', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['11', '12'])).
% 13.33/13.52  thf('147', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 13.33/13.52           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 13.33/13.52      inference('demod', [status(thm)], ['68', '69'])).
% 13.33/13.52  thf('148', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X3)))),
% 13.33/13.52      inference('sup+', [status(thm)], ['146', '147'])).
% 13.33/13.52  thf('149', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('demod', [status(thm)], ['20', '21'])).
% 13.33/13.52  thf('150', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 13.33/13.52           = (k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3))),
% 13.33/13.52      inference('demod', [status(thm)], ['148', '149'])).
% 13.33/13.52  thf('151', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.33/13.52         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.33/13.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.33/13.52              (k1_tarski @ X4)))),
% 13.33/13.52      inference('demod', [status(thm)], ['20', '21'])).
% 13.33/13.52  thf('152', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X0 @ X2 @ X1 @ X3)
% 13.33/13.52           = (k3_enumset1 @ X2 @ X1 @ X1 @ X0 @ X3))),
% 13.33/13.52      inference('demod', [status(thm)], ['145', '150', '151'])).
% 13.33/13.52  thf('153', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k2_enumset1 @ X0 @ X2 @ X1 @ X1) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 13.33/13.52      inference('demod', [status(thm)], ['142', '152'])).
% 13.33/13.52  thf('154', plain,
% 13.33/13.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 13.33/13.52      inference('sup+', [status(thm)], ['61', '62'])).
% 13.33/13.52  thf(t98_enumset1, axiom,
% 13.33/13.52    (![A:$i,B:$i,C:$i]:
% 13.33/13.52     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 13.33/13.52  thf('155', plain,
% 13.33/13.52      (![X56 : $i, X57 : $i, X58 : $i]:
% 13.33/13.52         ((k1_enumset1 @ X56 @ X58 @ X57) = (k1_enumset1 @ X56 @ X57 @ X58))),
% 13.33/13.52      inference('cnf', [status(esa)], [t98_enumset1])).
% 13.33/13.52  thf('156', plain,
% 13.33/13.52      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 13.33/13.52         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 13.33/13.52      inference('demod', [status(thm)],
% 13.33/13.52                ['3', '104', '113', '153', '154', '155'])).
% 13.33/13.52  thf('157', plain, ($false), inference('simplify', [status(thm)], ['156'])).
% 13.33/13.52  
% 13.33/13.52  % SZS output end Refutation
% 13.33/13.52  
% 13.33/13.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
