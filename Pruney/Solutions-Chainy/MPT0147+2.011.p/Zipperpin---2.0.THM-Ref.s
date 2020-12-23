%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LDt8KxbGWD

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  50 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  456 ( 498 expanded)
%              Number of equality atoms :   29 (  33 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(t63_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
        = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k4_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ ( k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
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

thf(t57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k5_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_xboole_0 @ ( k2_tarski @ X23 @ X24 ) @ ( k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t57_enumset1])).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(t62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('17',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k6_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_xboole_0 @ ( k1_tarski @ X30 ) @ ( k5_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t62_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('20',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['0','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LDt8KxbGWD
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:44:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 103 iterations in 0.092s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(sk_H_type, type, sk_H: $i).
% 0.21/0.55  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.21/0.55                                           $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.55  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.55  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.55  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.55  thf(t63_enumset1, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.55     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.55       ( k2_xboole_0 @
% 0.21/0.55         ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.55        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.55          ( k2_xboole_0 @
% 0.21/0.55            ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t63_enumset1])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.21/0.55         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.21/0.55             (k4_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t51_enumset1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.55     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.21/0.55       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.55         ((k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22)
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X17) @ 
% 0.21/0.55              (k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.21/0.55  thf(t41_enumset1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k2_tarski @ A @ B ) =
% 0.21/0.55       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i]:
% 0.21/0.55         ((k2_tarski @ X3 @ X4)
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_tarski @ X4)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i]:
% 0.21/0.55         ((k2_tarski @ X3 @ X4)
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_tarski @ X4)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.55  thf(t4_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.55       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.55           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.21/0.55              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['2', '5'])).
% 0.21/0.55  thf(t42_enumset1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.21/0.55       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.55         ((k1_enumset1 @ X5 @ X6 @ X7)
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k2_tarski @ X6 @ X7)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.55           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.55           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.21/0.55              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.21/0.55           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.21/0.55              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['1', '10'])).
% 0.21/0.55  thf(t57_enumset1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.55     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.55       ( k2_xboole_0 @
% 0.21/0.55         ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ))).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.55         ((k5_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29)
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X23 @ X24) @ 
% 0.21/0.55              (k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t57_enumset1])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.55         ((k1_enumset1 @ X5 @ X6 @ X7)
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k2_tarski @ X6 @ X7)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.55           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.21/0.55              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.21/0.55           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.21/0.55              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['12', '15'])).
% 0.21/0.55  thf(t62_enumset1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.55     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.55       ( k2_xboole_0 @
% 0.21/0.55         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, 
% 0.21/0.55         X37 : $i]:
% 0.21/0.55         ((k6_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X30) @ 
% 0.21/0.55              (k5_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t62_enumset1])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.55         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.55           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.21/0.55              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.55         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.21/0.55              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['11', '18'])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.21/0.55         != (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.21/0.55             sk_H))),
% 0.21/0.55      inference('demod', [status(thm)], ['0', '19'])).
% 0.21/0.55  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
