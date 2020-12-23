%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0KRSpA5nce

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:15 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   52 (  77 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  572 ( 859 expanded)
%              Number of equality atoms :   35 (  60 expanded)
%              Maximal formula depth    :   19 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t64_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
        = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) @ ( k3_enumset1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k4_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(demod,[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t56_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k5_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k1_tarski @ X19 ) @ ( k4_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t56_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('24',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k6_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k1_tarski @ X26 ) @ ( k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t62_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['12','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0KRSpA5nce
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 21:02:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.41/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.58  % Solved by: fo/fo7.sh
% 0.41/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.58  % done 63 iterations in 0.096s
% 0.41/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.58  % SZS output start Refutation
% 0.41/0.58  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.41/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.58  thf(sk_H_type, type, sk_H: $i).
% 0.41/0.58  thf(sk_F_type, type, sk_F: $i).
% 0.41/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.58  thf(sk_G_type, type, sk_G: $i).
% 0.41/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.58  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.41/0.58                                           $i > $i).
% 0.41/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.41/0.58  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.41/0.58  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.41/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.58  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.41/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.58  thf(t64_enumset1, conjecture,
% 0.41/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.41/0.58     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.41/0.58       ( k2_xboole_0 @
% 0.41/0.58         ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ))).
% 0.41/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.58    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.41/0.58        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.41/0.58          ( k2_xboole_0 @
% 0.41/0.58            ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ) )),
% 0.41/0.58    inference('cnf.neg', [status(esa)], [t64_enumset1])).
% 0.41/0.58  thf('0', plain,
% 0.41/0.58      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.41/0.58         != (k2_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_C) @ 
% 0.41/0.58             (k3_enumset1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(t51_enumset1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.41/0.58     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.41/0.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.41/0.58  thf('1', plain,
% 0.41/0.58      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.41/0.58         ((k4_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.41/0.58           = (k2_xboole_0 @ (k1_tarski @ X13) @ 
% 0.41/0.58              (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.41/0.58  thf(t41_enumset1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( k2_tarski @ A @ B ) =
% 0.41/0.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.41/0.58  thf('2', plain,
% 0.41/0.58      (![X8 : $i, X9 : $i]:
% 0.41/0.58         ((k2_tarski @ X8 @ X9)
% 0.41/0.58           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k1_tarski @ X9)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.41/0.58  thf('3', plain,
% 0.41/0.58      (![X8 : $i, X9 : $i]:
% 0.41/0.58         ((k2_tarski @ X8 @ X9)
% 0.41/0.58           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k1_tarski @ X9)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.41/0.58  thf(t4_xboole_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.41/0.58       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.41/0.58  thf('4', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.41/0.58           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.41/0.58  thf('5', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.41/0.58           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.41/0.58              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['3', '4'])).
% 0.41/0.58  thf('6', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.41/0.58           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['2', '5'])).
% 0.41/0.58  thf(t42_enumset1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.41/0.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.41/0.58  thf('7', plain,
% 0.41/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.58         ((k1_enumset1 @ X10 @ X11 @ X12)
% 0.41/0.58           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k2_tarski @ X11 @ X12)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.41/0.58  thf('8', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.41/0.58           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.41/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.41/0.58  thf('9', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.41/0.58           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.41/0.58  thf('10', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.58         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.41/0.58           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.41/0.58              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['8', '9'])).
% 0.41/0.58  thf('11', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.58         ((k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.41/0.58           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.41/0.58           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.41/0.58              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['1', '10'])).
% 0.41/0.58  thf('12', plain,
% 0.41/0.58      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.41/0.58         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.41/0.58             (k4_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.41/0.58      inference('demod', [status(thm)], ['0', '11'])).
% 0.41/0.58  thf('13', plain,
% 0.41/0.58      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.41/0.58         ((k4_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.41/0.58           = (k2_xboole_0 @ (k1_tarski @ X13) @ 
% 0.41/0.58              (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.41/0.58  thf('14', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.41/0.58           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.41/0.58              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['3', '4'])).
% 0.41/0.58  thf('15', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.58         ((k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.41/0.58           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.41/0.58           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.41/0.58              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.58  thf(t56_enumset1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.41/0.58     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.41/0.58       ( k2_xboole_0 @
% 0.41/0.58         ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ))).
% 0.41/0.58  thf('16', plain,
% 0.41/0.58      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.41/0.58         ((k5_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25)
% 0.41/0.58           = (k2_xboole_0 @ (k1_tarski @ X19) @ 
% 0.41/0.58              (k4_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t56_enumset1])).
% 0.41/0.58  thf('17', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.58         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.41/0.58           = (k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.41/0.58              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['15', '16'])).
% 0.41/0.58  thf('18', plain,
% 0.41/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.58         ((k1_enumset1 @ X10 @ X11 @ X12)
% 0.41/0.58           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k2_tarski @ X11 @ X12)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.41/0.58  thf('19', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.41/0.58           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.41/0.58  thf('20', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.58         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.41/0.58           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.41/0.58              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['18', '19'])).
% 0.41/0.58  thf('21', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.58         ((k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.41/0.58           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.41/0.58           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.41/0.58              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['17', '20'])).
% 0.41/0.58  thf('22', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.58         ((k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.41/0.58           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.41/0.58           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.41/0.58              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['1', '10'])).
% 0.41/0.58  thf('23', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.58         ((k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.41/0.58           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.41/0.58           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.41/0.58              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.41/0.58      inference('demod', [status(thm)], ['21', '22'])).
% 0.41/0.58  thf(t62_enumset1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.41/0.58     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.41/0.58       ( k2_xboole_0 @
% 0.41/0.58         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.41/0.58  thf('24', plain,
% 0.41/0.58      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, 
% 0.41/0.58         X33 : $i]:
% 0.41/0.58         ((k6_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.41/0.58           = (k2_xboole_0 @ (k1_tarski @ X26) @ 
% 0.41/0.58              (k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t62_enumset1])).
% 0.41/0.58  thf('25', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.58         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.41/0.58           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.41/0.58              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['23', '24'])).
% 0.41/0.58  thf('26', plain,
% 0.41/0.58      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.41/0.58         != (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.41/0.58             sk_H))),
% 0.41/0.58      inference('demod', [status(thm)], ['12', '25'])).
% 0.41/0.58  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.41/0.58  
% 0.41/0.58  % SZS output end Refutation
% 0.41/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
