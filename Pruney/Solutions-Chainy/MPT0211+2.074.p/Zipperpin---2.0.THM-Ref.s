%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RvxR5fSLCg

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:39 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 571 expanded)
%              Number of leaves         :   24 ( 205 expanded)
%              Depth                    :   13
%              Number of atoms          : 1429 (8041 expanded)
%              Number of equality atoms :  109 ( 558 expanded)
%              Maximal formula depth    :   19 (  11 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X29 @ X29 @ X30 @ X31 )
      = ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('7',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k6_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 )
      = ( k5_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('8',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k5_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 )
      = ( k4_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('10',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k4_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k3_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k6_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 ) @ ( k2_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X6 @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('14',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k3_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k4_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k3_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('18',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k3_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['3','19'])).

thf('21',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X29 @ X29 @ X30 @ X31 )
      = ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X8 @ X7 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X29 @ X29 @ X30 @ X31 )
      = ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X6 @ X4 @ X5 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('29',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k6_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 ) @ ( k2_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k4_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k3_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('34',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k3_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X2 @ X0 @ X3 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['27','35'])).

thf('37',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k4_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k3_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X2 @ X0 @ X3 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('40',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X29 @ X29 @ X30 @ X31 )
      = ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('41',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X6 @ X4 @ X5 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X0 @ X1 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k4_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k3_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X2 @ X0 @ X1 @ X4 @ X3 )
      = ( k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('50',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k5_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 )
      = ( k4_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('51',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k6_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k6_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X2 @ X0 @ X1 @ X4 @ X3 )
      = ( k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k3_enumset1 @ X4 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k3_enumset1 @ X3 @ X1 @ X3 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','58'])).

thf('60',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X29 @ X29 @ X30 @ X31 )
      = ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('61',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X6 @ X4 @ X5 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('62',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X0 @ X0 @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('68',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k4_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k3_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k3_enumset1 @ X0 @ X1 @ X0 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('72',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X29 @ X29 @ X30 @ X31 )
      = ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X0 @ X2 @ X3 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k4_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k3_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X2 @ X3 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','69'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X2 @ X3 )
      = ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['38','70','79'])).

thf('81',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k4_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k3_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k3_enumset1 @ X4 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k3_enumset1 @ X0 @ X1 @ X0 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k3_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X8 @ X7 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('89',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X6 @ X4 @ X5 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X29 @ X29 @ X30 @ X31 )
      = ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('95',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','80','93','94'])).

thf('96',plain,(
    $false ),
    inference(simplify,[status(thm)],['95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RvxR5fSLCg
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:13:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.26/1.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.26/1.45  % Solved by: fo/fo7.sh
% 1.26/1.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.26/1.45  % done 2291 iterations in 0.994s
% 1.26/1.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.26/1.45  % SZS output start Refutation
% 1.26/1.45  thf(sk_C_type, type, sk_C: $i).
% 1.26/1.45  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.26/1.45  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.26/1.45  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.26/1.45  thf(sk_A_type, type, sk_A: $i).
% 1.26/1.45  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.26/1.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.26/1.45  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 1.26/1.45                                           $i > $i).
% 1.26/1.45  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 1.26/1.45  thf(sk_B_type, type, sk_B: $i).
% 1.26/1.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.26/1.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.26/1.45  thf(t137_enumset1, conjecture,
% 1.26/1.45    (![A:$i,B:$i,C:$i]:
% 1.26/1.45     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 1.26/1.45       ( k1_enumset1 @ A @ B @ C ) ))).
% 1.26/1.45  thf(zf_stmt_0, negated_conjecture,
% 1.26/1.45    (~( ![A:$i,B:$i,C:$i]:
% 1.26/1.45        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 1.26/1.45          ( k1_enumset1 @ A @ B @ C ) ) )),
% 1.26/1.45    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 1.26/1.45  thf('0', plain,
% 1.26/1.45      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 1.26/1.45         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 1.26/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.45  thf(t100_enumset1, axiom,
% 1.26/1.45    (![A:$i,B:$i,C:$i]:
% 1.26/1.45     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 1.26/1.45  thf('1', plain,
% 1.26/1.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.26/1.45         ((k1_enumset1 @ X6 @ X4 @ X5) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 1.26/1.45      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.26/1.45  thf('2', plain,
% 1.26/1.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.26/1.45         ((k1_enumset1 @ X6 @ X4 @ X5) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 1.26/1.45      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.26/1.45  thf('3', plain,
% 1.26/1.45      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 1.26/1.45         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 1.26/1.45      inference('demod', [status(thm)], ['0', '1', '2'])).
% 1.26/1.45  thf(t71_enumset1, axiom,
% 1.26/1.45    (![A:$i,B:$i,C:$i]:
% 1.26/1.45     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.26/1.45  thf('4', plain,
% 1.26/1.45      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.26/1.45         ((k2_enumset1 @ X29 @ X29 @ X30 @ X31)
% 1.26/1.45           = (k1_enumset1 @ X29 @ X30 @ X31))),
% 1.26/1.45      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.26/1.45  thf(t70_enumset1, axiom,
% 1.26/1.45    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.26/1.45  thf('5', plain,
% 1.26/1.45      (![X27 : $i, X28 : $i]:
% 1.26/1.45         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 1.26/1.45      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.26/1.45  thf('6', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.26/1.45      inference('sup+', [status(thm)], ['4', '5'])).
% 1.26/1.45  thf(t75_enumset1, axiom,
% 1.26/1.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.26/1.45     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 1.26/1.45       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 1.26/1.45  thf('7', plain,
% 1.26/1.45      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 1.26/1.45         ((k6_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53)
% 1.26/1.45           = (k5_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53))),
% 1.26/1.45      inference('cnf', [status(esa)], [t75_enumset1])).
% 1.26/1.45  thf(t74_enumset1, axiom,
% 1.26/1.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.26/1.45     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 1.26/1.45       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 1.26/1.45  thf('8', plain,
% 1.26/1.45      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.26/1.45         ((k5_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46)
% 1.26/1.45           = (k4_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46))),
% 1.26/1.45      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.26/1.45  thf('9', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.26/1.45         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 1.26/1.45           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.26/1.45      inference('sup+', [status(thm)], ['7', '8'])).
% 1.26/1.45  thf(t73_enumset1, axiom,
% 1.26/1.45    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.26/1.45     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.26/1.45       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.26/1.45  thf('10', plain,
% 1.26/1.45      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.26/1.45         ((k4_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40)
% 1.26/1.45           = (k3_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40))),
% 1.26/1.45      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.26/1.45  thf(t67_enumset1, axiom,
% 1.26/1.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.26/1.45     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 1.26/1.45       ( k2_xboole_0 @
% 1.26/1.45         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 1.26/1.45  thf('11', plain,
% 1.26/1.45      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, 
% 1.26/1.45         X17 : $i]:
% 1.26/1.45         ((k6_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17)
% 1.26/1.45           = (k2_xboole_0 @ 
% 1.26/1.45              (k4_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15) @ 
% 1.26/1.45              (k2_tarski @ X16 @ X17)))),
% 1.26/1.45      inference('cnf', [status(esa)], [t67_enumset1])).
% 1.26/1.45  thf('12', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.26/1.45         ((k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5)
% 1.26/1.45           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 1.26/1.45              (k2_tarski @ X6 @ X5)))),
% 1.26/1.45      inference('sup+', [status(thm)], ['10', '11'])).
% 1.26/1.45  thf('13', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.26/1.45         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 1.26/1.45           = (k2_xboole_0 @ (k3_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2) @ 
% 1.26/1.45              (k2_tarski @ X1 @ X0)))),
% 1.26/1.45      inference('sup+', [status(thm)], ['9', '12'])).
% 1.26/1.45  thf(t72_enumset1, axiom,
% 1.26/1.45    (![A:$i,B:$i,C:$i,D:$i]:
% 1.26/1.45     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.26/1.45  thf('14', plain,
% 1.26/1.45      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.26/1.45         ((k3_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35)
% 1.26/1.45           = (k2_enumset1 @ X32 @ X33 @ X34 @ X35))),
% 1.26/1.45      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.26/1.45  thf('15', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.26/1.45         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 1.26/1.45           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 1.26/1.45              (k2_tarski @ X1 @ X0)))),
% 1.26/1.45      inference('demod', [status(thm)], ['13', '14'])).
% 1.26/1.45  thf('16', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.26/1.45         ((k4_enumset1 @ X1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 1.26/1.45           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 1.26/1.45      inference('sup+', [status(thm)], ['6', '15'])).
% 1.26/1.45  thf('17', plain,
% 1.26/1.45      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.26/1.45         ((k4_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40)
% 1.26/1.45           = (k3_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40))),
% 1.26/1.45      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.26/1.45  thf('18', plain,
% 1.26/1.45      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.26/1.45         ((k3_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35)
% 1.26/1.45           = (k2_enumset1 @ X32 @ X33 @ X34 @ X35))),
% 1.26/1.45      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.26/1.45  thf('19', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.26/1.45         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 1.26/1.45           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 1.26/1.45      inference('demod', [status(thm)], ['16', '17', '18'])).
% 1.26/1.45  thf('20', plain,
% 1.26/1.45      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 1.26/1.45         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 1.26/1.45      inference('demod', [status(thm)], ['3', '19'])).
% 1.26/1.45  thf('21', plain,
% 1.26/1.45      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.26/1.45         ((k2_enumset1 @ X29 @ X29 @ X30 @ X31)
% 1.26/1.45           = (k1_enumset1 @ X29 @ X30 @ X31))),
% 1.26/1.45      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.26/1.45  thf(t102_enumset1, axiom,
% 1.26/1.45    (![A:$i,B:$i,C:$i]:
% 1.26/1.45     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 1.26/1.45  thf('22', plain,
% 1.26/1.45      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.26/1.45         ((k1_enumset1 @ X9 @ X8 @ X7) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 1.26/1.45      inference('cnf', [status(esa)], [t102_enumset1])).
% 1.26/1.45  thf('23', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.45         ((k1_enumset1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 1.26/1.45      inference('sup+', [status(thm)], ['21', '22'])).
% 1.26/1.45  thf('24', plain,
% 1.26/1.45      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.26/1.45         ((k2_enumset1 @ X29 @ X29 @ X30 @ X31)
% 1.26/1.45           = (k1_enumset1 @ X29 @ X30 @ X31))),
% 1.26/1.45      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.26/1.45  thf('25', plain,
% 1.26/1.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.26/1.45         ((k1_enumset1 @ X6 @ X4 @ X5) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 1.26/1.45      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.26/1.45  thf('26', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.45         ((k1_enumset1 @ X0 @ X2 @ X1) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 1.26/1.45      inference('sup+', [status(thm)], ['24', '25'])).
% 1.26/1.45  thf('27', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.45         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X1 @ X2 @ X0))),
% 1.26/1.45      inference('sup+', [status(thm)], ['23', '26'])).
% 1.26/1.45  thf('28', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.26/1.45         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 1.26/1.45           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.26/1.45      inference('sup+', [status(thm)], ['7', '8'])).
% 1.26/1.45  thf(t69_enumset1, axiom,
% 1.26/1.45    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.26/1.45  thf('29', plain,
% 1.26/1.45      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.26/1.45      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.26/1.45  thf('30', plain,
% 1.26/1.45      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, 
% 1.26/1.45         X17 : $i]:
% 1.26/1.45         ((k6_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17)
% 1.26/1.45           = (k2_xboole_0 @ 
% 1.26/1.45              (k4_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15) @ 
% 1.26/1.45              (k2_tarski @ X16 @ X17)))),
% 1.26/1.45      inference('cnf', [status(esa)], [t67_enumset1])).
% 1.26/1.45  thf('31', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.26/1.45         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 1.26/1.45           = (k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 1.26/1.45              (k1_tarski @ X0)))),
% 1.26/1.45      inference('sup+', [status(thm)], ['29', '30'])).
% 1.26/1.45  thf('32', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.26/1.45         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 1.26/1.45           = (k2_xboole_0 @ (k4_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 1.26/1.45              (k1_tarski @ X0)))),
% 1.26/1.45      inference('sup+', [status(thm)], ['28', '31'])).
% 1.26/1.45  thf('33', plain,
% 1.26/1.45      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.26/1.45         ((k4_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40)
% 1.26/1.45           = (k3_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40))),
% 1.26/1.45      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.26/1.45  thf('34', plain,
% 1.26/1.45      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.26/1.45         ((k3_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35)
% 1.26/1.45           = (k2_enumset1 @ X32 @ X33 @ X34 @ X35))),
% 1.26/1.45      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.26/1.45  thf('35', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.26/1.45         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 1.26/1.45           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 1.26/1.45              (k1_tarski @ X0)))),
% 1.26/1.45      inference('demod', [status(thm)], ['32', '33', '34'])).
% 1.26/1.45  thf('36', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.26/1.45         ((k4_enumset1 @ X1 @ X1 @ X2 @ X0 @ X3 @ X3)
% 1.26/1.45           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 1.26/1.45              (k1_tarski @ X3)))),
% 1.26/1.45      inference('sup+', [status(thm)], ['27', '35'])).
% 1.26/1.45  thf('37', plain,
% 1.26/1.45      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.26/1.45         ((k4_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40)
% 1.26/1.45           = (k3_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40))),
% 1.26/1.45      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.26/1.45  thf('38', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.26/1.45         ((k3_enumset1 @ X1 @ X2 @ X0 @ X3 @ X3)
% 1.26/1.45           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 1.26/1.45              (k1_tarski @ X3)))),
% 1.26/1.45      inference('demod', [status(thm)], ['36', '37'])).
% 1.26/1.45  thf('39', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.45         ((k1_enumset1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 1.26/1.45      inference('sup+', [status(thm)], ['21', '22'])).
% 1.26/1.45  thf('40', plain,
% 1.26/1.45      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.26/1.45         ((k2_enumset1 @ X29 @ X29 @ X30 @ X31)
% 1.26/1.45           = (k1_enumset1 @ X29 @ X30 @ X31))),
% 1.26/1.45      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.26/1.45  thf('41', plain,
% 1.26/1.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.26/1.45         ((k1_enumset1 @ X6 @ X4 @ X5) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 1.26/1.45      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.26/1.45  thf('42', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.45         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 1.26/1.45      inference('sup+', [status(thm)], ['40', '41'])).
% 1.26/1.45  thf('43', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.45         ((k2_enumset1 @ X2 @ X2 @ X0 @ X1) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 1.26/1.45      inference('sup+', [status(thm)], ['39', '42'])).
% 1.26/1.45  thf('44', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.26/1.45         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 1.26/1.45           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 1.26/1.45              (k2_tarski @ X1 @ X0)))),
% 1.26/1.45      inference('demod', [status(thm)], ['13', '14'])).
% 1.26/1.45  thf('45', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.26/1.45         ((k4_enumset1 @ X2 @ X2 @ X0 @ X1 @ X4 @ X3)
% 1.26/1.45           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 1.26/1.45              (k2_tarski @ X4 @ X3)))),
% 1.26/1.45      inference('sup+', [status(thm)], ['43', '44'])).
% 1.26/1.45  thf('46', plain,
% 1.26/1.45      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.26/1.45         ((k4_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40)
% 1.26/1.45           = (k3_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40))),
% 1.26/1.45      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.26/1.45  thf('47', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.26/1.45         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 1.26/1.45           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 1.26/1.45              (k2_tarski @ X1 @ X0)))),
% 1.26/1.45      inference('demod', [status(thm)], ['13', '14'])).
% 1.26/1.45  thf('48', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.26/1.45         ((k3_enumset1 @ X2 @ X0 @ X1 @ X4 @ X3)
% 1.26/1.45           = (k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3))),
% 1.26/1.45      inference('demod', [status(thm)], ['45', '46', '47'])).
% 1.26/1.45  thf('49', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.26/1.45         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 1.26/1.45           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.26/1.45      inference('sup+', [status(thm)], ['7', '8'])).
% 1.26/1.45  thf('50', plain,
% 1.26/1.45      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.26/1.45         ((k5_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46)
% 1.26/1.45           = (k4_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46))),
% 1.26/1.45      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.26/1.45  thf(t68_enumset1, axiom,
% 1.26/1.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.26/1.45     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 1.26/1.45       ( k2_xboole_0 @
% 1.26/1.45         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 1.26/1.45  thf('51', plain,
% 1.26/1.45      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, 
% 1.26/1.45         X25 : $i]:
% 1.26/1.45         ((k6_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25)
% 1.26/1.45           = (k2_xboole_0 @ 
% 1.26/1.45              (k5_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24) @ 
% 1.26/1.45              (k1_tarski @ X25)))),
% 1.26/1.45      inference('cnf', [status(esa)], [t68_enumset1])).
% 1.26/1.45  thf('52', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.26/1.45         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 1.26/1.45           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 1.26/1.45              (k1_tarski @ X6)))),
% 1.26/1.45      inference('sup+', [status(thm)], ['50', '51'])).
% 1.26/1.45  thf('53', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.26/1.45         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 1.26/1.45           = (k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 1.26/1.45              (k1_tarski @ X0)))),
% 1.26/1.45      inference('sup+', [status(thm)], ['29', '30'])).
% 1.26/1.45  thf('54', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.26/1.45         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 1.26/1.45           = (k6_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.26/1.45      inference('sup+', [status(thm)], ['52', '53'])).
% 1.26/1.45  thf('55', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.26/1.45         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 1.26/1.45           = (k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.26/1.45      inference('sup+', [status(thm)], ['49', '54'])).
% 1.26/1.45  thf('56', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.26/1.45         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 1.26/1.45           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.26/1.45      inference('sup+', [status(thm)], ['7', '8'])).
% 1.26/1.45  thf('57', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.26/1.45         ((k3_enumset1 @ X2 @ X0 @ X1 @ X4 @ X3)
% 1.26/1.45           = (k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3))),
% 1.26/1.45      inference('demod', [status(thm)], ['45', '46', '47'])).
% 1.26/1.45  thf('58', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.26/1.45         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 1.26/1.45           = (k3_enumset1 @ X4 @ X2 @ X3 @ X1 @ X0))),
% 1.26/1.45      inference('demod', [status(thm)], ['55', '56', '57'])).
% 1.26/1.45  thf('59', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.26/1.45         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 1.26/1.45           = (k3_enumset1 @ X3 @ X1 @ X3 @ X2 @ X0))),
% 1.26/1.45      inference('sup+', [status(thm)], ['48', '58'])).
% 1.26/1.45  thf('60', plain,
% 1.26/1.45      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.26/1.45         ((k2_enumset1 @ X29 @ X29 @ X30 @ X31)
% 1.26/1.45           = (k1_enumset1 @ X29 @ X30 @ X31))),
% 1.26/1.45      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.26/1.45  thf('61', plain,
% 1.26/1.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.26/1.45         ((k1_enumset1 @ X6 @ X4 @ X5) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 1.26/1.45      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.26/1.45  thf('62', plain,
% 1.26/1.45      (![X27 : $i, X28 : $i]:
% 1.26/1.45         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 1.26/1.45      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.26/1.45  thf('63', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.26/1.45      inference('sup+', [status(thm)], ['61', '62'])).
% 1.26/1.45  thf('64', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i]:
% 1.26/1.45         ((k2_enumset1 @ X0 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.26/1.45      inference('sup+', [status(thm)], ['60', '63'])).
% 1.26/1.45  thf('65', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.26/1.45         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 1.26/1.45           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 1.26/1.45      inference('demod', [status(thm)], ['16', '17', '18'])).
% 1.26/1.45  thf('66', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.26/1.45         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2)
% 1.26/1.45           = (k2_xboole_0 @ (k2_enumset1 @ X0 @ X0 @ X1 @ X0) @ 
% 1.26/1.45              (k2_tarski @ X3 @ X2)))),
% 1.26/1.45      inference('sup+', [status(thm)], ['64', '65'])).
% 1.26/1.45  thf('67', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.26/1.45         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 1.26/1.45           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 1.26/1.45              (k2_tarski @ X1 @ X0)))),
% 1.26/1.45      inference('demod', [status(thm)], ['13', '14'])).
% 1.26/1.45  thf('68', plain,
% 1.26/1.45      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.26/1.45         ((k4_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40)
% 1.26/1.45           = (k3_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40))),
% 1.26/1.45      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.26/1.45  thf('69', plain,
% 1.26/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.26/1.45         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2)
% 1.26/1.45           = (k3_enumset1 @ X0 @ X1 @ X0 @ X3 @ X2))),
% 1.26/1.45      inference('demod', [status(thm)], ['66', '67', '68'])).
% 1.26/1.45  thf('70', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.26/1.46         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 1.26/1.46           = (k2_enumset1 @ X3 @ X1 @ X2 @ X0))),
% 1.26/1.46      inference('demod', [status(thm)], ['59', '69'])).
% 1.26/1.46  thf('71', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.46         ((k1_enumset1 @ X0 @ X2 @ X1) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['24', '25'])).
% 1.26/1.46  thf('72', plain,
% 1.26/1.46      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.26/1.46         ((k2_enumset1 @ X29 @ X29 @ X30 @ X31)
% 1.26/1.46           = (k1_enumset1 @ X29 @ X30 @ X31))),
% 1.26/1.46      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.26/1.46  thf('73', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.46         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['71', '72'])).
% 1.26/1.46  thf('74', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.26/1.46         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 1.26/1.46           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 1.26/1.46              (k1_tarski @ X0)))),
% 1.26/1.46      inference('demod', [status(thm)], ['32', '33', '34'])).
% 1.26/1.46  thf('75', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.26/1.46         ((k4_enumset1 @ X1 @ X1 @ X0 @ X2 @ X3 @ X3)
% 1.26/1.46           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 1.26/1.46              (k1_tarski @ X3)))),
% 1.26/1.46      inference('sup+', [status(thm)], ['73', '74'])).
% 1.26/1.46  thf('76', plain,
% 1.26/1.46      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.26/1.46         ((k4_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40)
% 1.26/1.46           = (k3_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40))),
% 1.26/1.46      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.26/1.46  thf('77', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.26/1.46         ((k3_enumset1 @ X1 @ X0 @ X2 @ X3 @ X3)
% 1.26/1.46           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 1.26/1.46              (k1_tarski @ X3)))),
% 1.26/1.46      inference('demod', [status(thm)], ['75', '76'])).
% 1.26/1.46  thf('78', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.26/1.46         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 1.26/1.46           = (k2_enumset1 @ X3 @ X1 @ X2 @ X0))),
% 1.26/1.46      inference('demod', [status(thm)], ['59', '69'])).
% 1.26/1.46  thf('79', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.26/1.46         ((k2_enumset1 @ X1 @ X2 @ X0 @ X3)
% 1.26/1.46           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 1.26/1.46              (k1_tarski @ X3)))),
% 1.26/1.46      inference('demod', [status(thm)], ['77', '78'])).
% 1.26/1.46  thf('80', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.26/1.46         ((k2_enumset1 @ X1 @ X0 @ X2 @ X3) = (k2_enumset1 @ X1 @ X2 @ X0 @ X3))),
% 1.26/1.46      inference('demod', [status(thm)], ['38', '70', '79'])).
% 1.26/1.46  thf('81', plain,
% 1.26/1.46      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.26/1.46         ((k4_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40)
% 1.26/1.46           = (k3_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40))),
% 1.26/1.46      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.26/1.46  thf('82', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.26/1.46         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 1.26/1.46           = (k3_enumset1 @ X4 @ X2 @ X3 @ X1 @ X0))),
% 1.26/1.46      inference('demod', [status(thm)], ['55', '56', '57'])).
% 1.26/1.46  thf('83', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.26/1.46         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 1.26/1.46           = (k3_enumset1 @ X3 @ X2 @ X3 @ X1 @ X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['81', '82'])).
% 1.26/1.46  thf('84', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.26/1.46         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2)
% 1.26/1.46           = (k3_enumset1 @ X0 @ X1 @ X0 @ X3 @ X2))),
% 1.26/1.46      inference('demod', [status(thm)], ['66', '67', '68'])).
% 1.26/1.46  thf('85', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.26/1.46         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 1.26/1.46           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.26/1.46      inference('demod', [status(thm)], ['83', '84'])).
% 1.26/1.46  thf('86', plain,
% 1.26/1.46      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.26/1.46         ((k3_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35)
% 1.26/1.46           = (k2_enumset1 @ X32 @ X33 @ X34 @ X35))),
% 1.26/1.46      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.26/1.46  thf('87', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.46         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X0 @ X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['85', '86'])).
% 1.26/1.46  thf('88', plain,
% 1.26/1.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.26/1.46         ((k1_enumset1 @ X9 @ X8 @ X7) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 1.26/1.46      inference('cnf', [status(esa)], [t102_enumset1])).
% 1.26/1.46  thf('89', plain,
% 1.26/1.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.26/1.46         ((k1_enumset1 @ X6 @ X4 @ X5) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 1.26/1.46      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.26/1.46  thf('90', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.46         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['88', '89'])).
% 1.26/1.46  thf('91', plain,
% 1.26/1.46      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.26/1.46         ((k2_enumset1 @ X29 @ X29 @ X30 @ X31)
% 1.26/1.46           = (k1_enumset1 @ X29 @ X30 @ X31))),
% 1.26/1.46      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.26/1.46  thf('92', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.46         ((k2_enumset1 @ X1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['90', '91'])).
% 1.26/1.46  thf('93', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.46         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['87', '92'])).
% 1.26/1.46  thf('94', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.46         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['88', '89'])).
% 1.26/1.46  thf('95', plain,
% 1.26/1.46      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 1.26/1.46         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 1.26/1.46      inference('demod', [status(thm)], ['20', '80', '93', '94'])).
% 1.26/1.46  thf('96', plain, ($false), inference('simplify', [status(thm)], ['95'])).
% 1.26/1.46  
% 1.26/1.46  % SZS output end Refutation
% 1.26/1.46  
% 1.26/1.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
