%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sYjJzf7RCo

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 (  87 expanded)
%              Number of leaves         :   19 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  601 ( 934 expanded)
%              Number of equality atoms :   42 (  73 expanded)
%              Maximal formula depth    :   17 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t60_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
        ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
        = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_enumset1])).

thf('0',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k2_xboole_0 @ ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k2_tarski @ sk_F @ sk_G ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) @ X4 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X4 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X4 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','20'])).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k3_enumset1 @ X3 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X4 @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k5_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k2_tarski @ X13 @ X14 ) @ ( k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t57_enumset1])).

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k3_enumset1 @ X3 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X4 @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','28','29','32'])).

thf('34',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['0','33'])).

thf('35',plain,(
    $false ),
    inference(simplify,[status(thm)],['34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sYjJzf7RCo
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 29 iterations in 0.024s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.47  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.47  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(t60_enumset1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.47     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.47       ( k2_xboole_0 @
% 0.20/0.47         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.47        ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.47          ( k2_xboole_0 @
% 0.20/0.47            ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t60_enumset1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.20/0.47         != (k2_xboole_0 @ (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47             (k2_tarski @ sk_F @ sk_G)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t42_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.47       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.47         ((k1_enumset1 @ X10 @ X11 @ X12)
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k2_tarski @ X11 @ X12)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.47  thf(t41_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( k2_tarski @ A @ B ) =
% 0.20/0.47       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i]:
% 0.20/0.47         ((k2_tarski @ X8 @ X9)
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k1_tarski @ X9)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.47  thf(t4_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.47       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.20/0.47           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.20/0.47              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['1', '4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i]:
% 0.20/0.47         ((k2_tarski @ X8 @ X9)
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k1_tarski @ X9)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.20/0.47              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.47         ((k1_enumset1 @ X10 @ X11 @ X12)
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k2_tarski @ X11 @ X12)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.47           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.20/0.47      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.47         ((k1_enumset1 @ X10 @ X11 @ X12)
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k2_tarski @ X11 @ X12)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.20/0.47           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.20/0.47              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['10', '13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['1', '4'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.47           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.20/0.47           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ 
% 0.20/0.47           (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)) @ X4)
% 0.20/0.47           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ 
% 0.20/0.47              (k2_xboole_0 @ (k1_tarski @ X0) @ X4)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.20/0.47           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 0.20/0.47           (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X4))
% 0.20/0.47           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ 
% 0.20/0.47              (k2_xboole_0 @ (k1_tarski @ X0) @ X4)))),
% 0.20/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.20/0.47           (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))
% 0.20/0.47           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 0.20/0.47              (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))))),
% 0.20/0.47      inference('sup+', [status(thm)], ['5', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.47         ((k1_enumset1 @ X10 @ X11 @ X12)
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k2_tarski @ X11 @ X12)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.47           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.20/0.47      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.20/0.47           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.20/0.47           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.20/0.47              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.20/0.47           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.20/0.47              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['22', '25'])).
% 0.20/0.47  thf(l57_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.47     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.20/0.47       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.47         ((k3_enumset1 @ X3 @ X4 @ X5 @ X6 @ X7)
% 0.20/0.47           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X4 @ X5) @ 
% 0.20/0.47              (k2_tarski @ X6 @ X7)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.47           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.20/0.47              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.47  thf(t57_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.47     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.47       ( k2_xboole_0 @
% 0.20/0.47         ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ))).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.47         ((k5_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.20/0.47           = (k2_xboole_0 @ (k2_tarski @ X13 @ X14) @ 
% 0.20/0.47              (k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t57_enumset1])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.47         ((k3_enumset1 @ X3 @ X4 @ X5 @ X6 @ X7)
% 0.20/0.47           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X4 @ X5) @ 
% 0.20/0.47              (k2_tarski @ X6 @ X7)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.20/0.47           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 0.20/0.47           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 0.20/0.47              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X5)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.47           = (k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.20/0.47              (k2_tarski @ X1 @ X0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['21', '28', '29', '32'])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.20/0.47         != (k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G))),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '33'])).
% 0.20/0.47  thf('35', plain, ($false), inference('simplify', [status(thm)], ['34'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
