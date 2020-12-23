%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.icGKLNepAE

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:26 EST 2020

% Result     : Theorem 0.95s
% Output     : Refutation 0.95s
% Verified   : 
% Statistics : Number of formulae       :   65 (  77 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  651 ( 804 expanded)
%              Number of equality atoms :   45 (  57 expanded)
%              Maximal formula depth    :   21 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_enumset1_type,type,(
    k7_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t128_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k5_enumset1 @ C @ D @ E @ F @ G @ H @ I ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
        ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
        = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k5_enumset1 @ C @ D @ E @ F @ G @ H @ I ) ) ) ),
    inference('cnf.neg',[status(esa)],[t128_enumset1])).

thf('0',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k6_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k1_tarski @ X28 ) @ ( k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t62_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t84_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( k4_enumset1 @ X54 @ X54 @ X54 @ X54 @ X55 @ X56 )
      = ( k1_enumset1 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t84_enumset1])).

thf(t79_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('6',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k4_enumset1 @ X50 @ X50 @ X50 @ X51 @ X52 @ X53 )
      = ( k2_enumset1 @ X50 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t79_enumset1])).

thf('7',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( k2_enumset1 @ X54 @ X54 @ X55 @ X56 )
      = ( k1_enumset1 @ X54 @ X55 @ X56 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('9',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k5_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k4_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('10',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k4_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 @ X43 )
      = ( k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k4_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 @ X43 )
      = ( k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k4_enumset1 @ X50 @ X50 @ X50 @ X51 @ X52 @ X53 )
      = ( k2_enumset1 @ X50 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t79_enumset1])).

thf('17',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k4_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 @ X43 )
      = ( k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('18',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k3_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 )
      = ( k2_enumset1 @ X50 @ X51 @ X52 @ X53 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','19'])).

thf('21',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k3_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 )
      = ( k2_enumset1 @ X50 @ X51 @ X52 @ X53 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( k2_enumset1 @ X54 @ X54 @ X55 @ X56 )
      = ( k1_enumset1 @ X54 @ X55 @ X56 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('24',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X8 @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','28'])).

thf(t127_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k6_enumset1 @ B @ C @ D @ E @ F @ G @ H @ I ) ) ) )).

thf('30',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k7_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k6_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t127_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X8 @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(demod,[status(thm)],['0','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.icGKLNepAE
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:37:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.95/1.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.95/1.16  % Solved by: fo/fo7.sh
% 0.95/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.95/1.16  % done 980 iterations in 0.719s
% 0.95/1.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.95/1.16  % SZS output start Refutation
% 0.95/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.95/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.95/1.16  thf(sk_E_type, type, sk_E: $i).
% 0.95/1.16  thf(sk_H_type, type, sk_H: $i).
% 0.95/1.16  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.95/1.16  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.95/1.16  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.95/1.16  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.95/1.16  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.95/1.16  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.95/1.16  thf(k7_enumset1_type, type, k7_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.95/1.16                                           $i > $i > $i).
% 0.95/1.16  thf(sk_F_type, type, sk_F: $i).
% 0.95/1.16  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.95/1.16  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.95/1.16                                           $i > $i).
% 0.95/1.16  thf(sk_C_type, type, sk_C: $i).
% 0.95/1.16  thf(sk_I_type, type, sk_I: $i).
% 0.95/1.16  thf(sk_G_type, type, sk_G: $i).
% 0.95/1.16  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.95/1.16  thf(sk_D_type, type, sk_D: $i).
% 0.95/1.16  thf(t128_enumset1, conjecture,
% 0.95/1.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.95/1.16     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.95/1.16       ( k2_xboole_0 @
% 0.95/1.16         ( k2_tarski @ A @ B ) @ ( k5_enumset1 @ C @ D @ E @ F @ G @ H @ I ) ) ))).
% 0.95/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.95/1.16    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.95/1.16        ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.95/1.16          ( k2_xboole_0 @
% 0.95/1.16            ( k2_tarski @ A @ B ) @ ( k5_enumset1 @ C @ D @ E @ F @ G @ H @ I ) ) ) )),
% 0.95/1.16    inference('cnf.neg', [status(esa)], [t128_enumset1])).
% 0.95/1.16  thf('0', plain,
% 0.95/1.16      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 0.95/1.16         sk_I)
% 0.95/1.16         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.95/1.16             (k5_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I)))),
% 0.95/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.16  thf(t62_enumset1, axiom,
% 0.95/1.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.95/1.16     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.95/1.16       ( k2_xboole_0 @
% 0.95/1.16         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.95/1.16  thf('1', plain,
% 0.95/1.16      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, 
% 0.95/1.16         X35 : $i]:
% 0.95/1.16         ((k6_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)
% 0.95/1.16           = (k2_xboole_0 @ (k1_tarski @ X28) @ 
% 0.95/1.16              (k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)))),
% 0.95/1.16      inference('cnf', [status(esa)], [t62_enumset1])).
% 0.95/1.16  thf(t70_enumset1, axiom,
% 0.95/1.16    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.95/1.16  thf('2', plain,
% 0.95/1.16      (![X37 : $i, X38 : $i]:
% 0.95/1.16         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 0.95/1.16      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.95/1.16  thf(t69_enumset1, axiom,
% 0.95/1.16    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.95/1.16  thf('3', plain, (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.95/1.16      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.95/1.16  thf('4', plain,
% 0.95/1.16      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.95/1.16      inference('sup+', [status(thm)], ['2', '3'])).
% 0.95/1.16  thf(t84_enumset1, axiom,
% 0.95/1.16    (![A:$i,B:$i,C:$i]:
% 0.95/1.16     ( ( k4_enumset1 @ A @ A @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.95/1.16  thf('5', plain,
% 0.95/1.16      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.95/1.16         ((k4_enumset1 @ X54 @ X54 @ X54 @ X54 @ X55 @ X56)
% 0.95/1.16           = (k1_enumset1 @ X54 @ X55 @ X56))),
% 0.95/1.16      inference('cnf', [status(esa)], [t84_enumset1])).
% 0.95/1.16  thf(t79_enumset1, axiom,
% 0.95/1.16    (![A:$i,B:$i,C:$i,D:$i]:
% 0.95/1.16     ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D ) =
% 0.95/1.16       ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.95/1.16  thf('6', plain,
% 0.95/1.16      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.95/1.16         ((k4_enumset1 @ X50 @ X50 @ X50 @ X51 @ X52 @ X53)
% 0.95/1.16           = (k2_enumset1 @ X50 @ X51 @ X52 @ X53))),
% 0.95/1.16      inference('cnf', [status(esa)], [t79_enumset1])).
% 0.95/1.16  thf('7', plain,
% 0.95/1.16      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.95/1.16         ((k2_enumset1 @ X54 @ X54 @ X55 @ X56)
% 0.95/1.16           = (k1_enumset1 @ X54 @ X55 @ X56))),
% 0.95/1.16      inference('demod', [status(thm)], ['5', '6'])).
% 0.95/1.16  thf('8', plain,
% 0.95/1.16      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.95/1.16      inference('sup+', [status(thm)], ['4', '7'])).
% 0.95/1.16  thf(t74_enumset1, axiom,
% 0.95/1.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.95/1.16     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.95/1.16       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.95/1.16  thf('9', plain,
% 0.95/1.16      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.95/1.16         ((k5_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49)
% 0.95/1.16           = (k4_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49))),
% 0.95/1.16      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.95/1.16  thf(t73_enumset1, axiom,
% 0.95/1.16    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.95/1.16     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.95/1.16       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.95/1.16  thf('10', plain,
% 0.95/1.16      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.95/1.16         ((k4_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 @ X43)
% 0.95/1.16           = (k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43))),
% 0.95/1.16      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.95/1.16  thf('11', plain,
% 0.95/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.95/1.16         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.95/1.16           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.95/1.16      inference('sup+', [status(thm)], ['9', '10'])).
% 0.95/1.16  thf('12', plain,
% 0.95/1.16      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.95/1.16         ((k4_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 @ X43)
% 0.95/1.16           = (k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43))),
% 0.95/1.16      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.95/1.16  thf(t61_enumset1, axiom,
% 0.95/1.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.95/1.16     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.95/1.16       ( k2_xboole_0 @
% 0.95/1.16         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 0.95/1.16  thf('13', plain,
% 0.95/1.16      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.95/1.16         ((k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.95/1.16           = (k2_xboole_0 @ 
% 0.95/1.16              (k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26) @ 
% 0.95/1.16              (k1_tarski @ X27)))),
% 0.95/1.16      inference('cnf', [status(esa)], [t61_enumset1])).
% 0.95/1.16  thf('14', plain,
% 0.95/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.95/1.16         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 0.95/1.16           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.95/1.16              (k1_tarski @ X5)))),
% 0.95/1.16      inference('sup+', [status(thm)], ['12', '13'])).
% 0.95/1.16  thf('15', plain,
% 0.95/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.95/1.16         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.95/1.16           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 0.95/1.16              (k1_tarski @ X0)))),
% 0.95/1.16      inference('sup+', [status(thm)], ['11', '14'])).
% 0.95/1.16  thf('16', plain,
% 0.95/1.16      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.95/1.16         ((k4_enumset1 @ X50 @ X50 @ X50 @ X51 @ X52 @ X53)
% 0.95/1.16           = (k2_enumset1 @ X50 @ X51 @ X52 @ X53))),
% 0.95/1.16      inference('cnf', [status(esa)], [t79_enumset1])).
% 0.95/1.16  thf('17', plain,
% 0.95/1.16      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.95/1.16         ((k4_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 @ X43)
% 0.95/1.16           = (k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43))),
% 0.95/1.16      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.95/1.16  thf('18', plain,
% 0.95/1.16      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.95/1.16         ((k3_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53)
% 0.95/1.16           = (k2_enumset1 @ X50 @ X51 @ X52 @ X53))),
% 0.95/1.16      inference('demod', [status(thm)], ['16', '17'])).
% 0.95/1.16  thf('19', plain,
% 0.95/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.95/1.16         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.95/1.16           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 0.95/1.16              (k1_tarski @ X0)))),
% 0.95/1.16      inference('demod', [status(thm)], ['15', '18'])).
% 0.95/1.16  thf('20', plain,
% 0.95/1.16      (![X0 : $i, X1 : $i]:
% 0.95/1.16         ((k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1)
% 0.95/1.16           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.95/1.16      inference('sup+', [status(thm)], ['8', '19'])).
% 0.95/1.16  thf('21', plain,
% 0.95/1.16      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.95/1.16         ((k3_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53)
% 0.95/1.16           = (k2_enumset1 @ X50 @ X51 @ X52 @ X53))),
% 0.95/1.16      inference('demod', [status(thm)], ['16', '17'])).
% 0.95/1.16  thf('22', plain,
% 0.95/1.16      (![X0 : $i, X1 : $i]:
% 0.95/1.16         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.95/1.16           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.95/1.16      inference('demod', [status(thm)], ['20', '21'])).
% 0.95/1.16  thf('23', plain,
% 0.95/1.16      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.95/1.16         ((k2_enumset1 @ X54 @ X54 @ X55 @ X56)
% 0.95/1.16           = (k1_enumset1 @ X54 @ X55 @ X56))),
% 0.95/1.16      inference('demod', [status(thm)], ['5', '6'])).
% 0.95/1.16  thf('24', plain,
% 0.95/1.16      (![X37 : $i, X38 : $i]:
% 0.95/1.16         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 0.95/1.16      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.95/1.16  thf('25', plain,
% 0.95/1.16      (![X0 : $i, X1 : $i]:
% 0.95/1.16         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.95/1.16      inference('sup+', [status(thm)], ['23', '24'])).
% 0.95/1.16  thf('26', plain,
% 0.95/1.16      (![X0 : $i, X1 : $i]:
% 0.95/1.16         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.95/1.16           = (k2_tarski @ X1 @ X0))),
% 0.95/1.16      inference('sup+', [status(thm)], ['22', '25'])).
% 0.95/1.16  thf(t4_xboole_1, axiom,
% 0.95/1.16    (![A:$i,B:$i,C:$i]:
% 0.95/1.16     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.95/1.16       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.95/1.16  thf('27', plain,
% 0.95/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.95/1.16         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.95/1.16           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.95/1.16      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.95/1.16  thf('28', plain,
% 0.95/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.95/1.16         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.95/1.16           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.95/1.16              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.95/1.16      inference('sup+', [status(thm)], ['26', '27'])).
% 0.95/1.16  thf('29', plain,
% 0.95/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.95/1.16         X7 : $i, X8 : $i]:
% 0.95/1.16         ((k2_xboole_0 @ (k2_tarski @ X8 @ X7) @ 
% 0.95/1.16           (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.95/1.16           = (k2_xboole_0 @ (k1_tarski @ X8) @ 
% 0.95/1.16              (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.95/1.16      inference('sup+', [status(thm)], ['1', '28'])).
% 0.95/1.16  thf(t127_enumset1, axiom,
% 0.95/1.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.95/1.16     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.95/1.16       ( k2_xboole_0 @
% 0.95/1.16         ( k1_tarski @ A ) @ ( k6_enumset1 @ B @ C @ D @ E @ F @ G @ H @ I ) ) ))).
% 0.95/1.16  thf('30', plain,
% 0.95/1.16      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, 
% 0.95/1.16         X19 : $i, X20 : $i]:
% 0.95/1.16         ((k7_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.95/1.16           = (k2_xboole_0 @ (k1_tarski @ X12) @ 
% 0.95/1.16              (k6_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)))),
% 0.95/1.16      inference('cnf', [status(esa)], [t127_enumset1])).
% 0.95/1.16  thf('31', plain,
% 0.95/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.95/1.16         X7 : $i, X8 : $i]:
% 0.95/1.16         ((k2_xboole_0 @ (k2_tarski @ X8 @ X7) @ 
% 0.95/1.16           (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.95/1.16           = (k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.95/1.16      inference('demod', [status(thm)], ['29', '30'])).
% 0.95/1.16  thf('32', plain,
% 0.95/1.16      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 0.95/1.16         sk_I)
% 0.95/1.16         != (k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.95/1.16             sk_H @ sk_I))),
% 0.95/1.16      inference('demod', [status(thm)], ['0', '31'])).
% 0.95/1.16  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.95/1.16  
% 0.95/1.16  % SZS output end Refutation
% 0.95/1.16  
% 0.95/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
