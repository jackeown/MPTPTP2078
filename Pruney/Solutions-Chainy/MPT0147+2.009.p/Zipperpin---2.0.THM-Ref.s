%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OzhqFHsddv

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  50 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  458 ( 500 expanded)
%              Number of equality atoms :   29 (  33 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

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

thf(t57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k5_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k2_tarski @ X25 @ X26 ) @ ( k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t57_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k2_tarski @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k2_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k4_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X19 ) @ ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k2_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k2_tarski @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k2_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','16'])).

thf(t62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('18',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k6_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k5_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t62_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['0','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OzhqFHsddv
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:51:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.60  % Solved by: fo/fo7.sh
% 0.21/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.60  % done 86 iterations in 0.150s
% 0.21/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.60  % SZS output start Refutation
% 0.21/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.60  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.60  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.21/0.60                                           $i > $i).
% 0.21/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.60  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.60  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.60  thf(sk_H_type, type, sk_H: $i).
% 0.21/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.60  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.60  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.60  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.60  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.60  thf(t63_enumset1, conjecture,
% 0.21/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.60     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.60       ( k2_xboole_0 @
% 0.21/0.60         ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.21/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.60    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.60        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.60          ( k2_xboole_0 @
% 0.21/0.60            ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ) )),
% 0.21/0.60    inference('cnf.neg', [status(esa)], [t63_enumset1])).
% 0.21/0.60  thf('0', plain,
% 0.21/0.60      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.21/0.60         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.21/0.60             (k4_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(t57_enumset1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.60     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.60       ( k2_xboole_0 @
% 0.21/0.60         ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ))).
% 0.21/0.60  thf('1', plain,
% 0.21/0.60      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.60         ((k5_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.21/0.60           = (k2_xboole_0 @ (k2_tarski @ X25 @ X26) @ 
% 0.21/0.60              (k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t57_enumset1])).
% 0.21/0.60  thf(t42_enumset1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.21/0.60       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.21/0.60  thf('2', plain,
% 0.21/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.60         ((k1_enumset1 @ X16 @ X17 @ X18)
% 0.21/0.60           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k2_tarski @ X17 @ X18)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.60  thf(t4_xboole_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.60       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.60  thf('3', plain,
% 0.21/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.60         ((k2_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X8)
% 0.21/0.60           = (k2_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.60  thf('4', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.60         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.21/0.60           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.21/0.60              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 0.21/0.60      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.60  thf('5', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.60         ((k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.21/0.60           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.60           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.21/0.60              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.60      inference('sup+', [status(thm)], ['1', '4'])).
% 0.21/0.60  thf(t51_enumset1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.60     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.21/0.60       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.21/0.60  thf('6', plain,
% 0.21/0.60      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.60         ((k4_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.21/0.60           = (k2_xboole_0 @ (k1_tarski @ X19) @ 
% 0.21/0.60              (k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.21/0.60  thf(t41_enumset1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( k2_tarski @ A @ B ) =
% 0.21/0.60       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.60  thf('7', plain,
% 0.21/0.60      (![X14 : $i, X15 : $i]:
% 0.21/0.60         ((k2_tarski @ X14 @ X15)
% 0.21/0.60           = (k2_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X15)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.60  thf('8', plain,
% 0.21/0.60      (![X14 : $i, X15 : $i]:
% 0.21/0.60         ((k2_tarski @ X14 @ X15)
% 0.21/0.60           = (k2_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X15)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.60  thf('9', plain,
% 0.21/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.60         ((k2_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X8)
% 0.21/0.60           = (k2_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.60  thf('10', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.60           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.21/0.60              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.21/0.60      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.60  thf('11', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.60           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.60      inference('sup+', [status(thm)], ['7', '10'])).
% 0.21/0.60  thf('12', plain,
% 0.21/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.60         ((k1_enumset1 @ X16 @ X17 @ X18)
% 0.21/0.60           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k2_tarski @ X17 @ X18)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.60  thf('13', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.60           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.60      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.60  thf('14', plain,
% 0.21/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.60         ((k2_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X8)
% 0.21/0.60           = (k2_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.60  thf('15', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.60         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.21/0.60           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.21/0.60              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.21/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.60  thf('16', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.60         ((k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.21/0.60           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.60           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.21/0.60              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.60      inference('sup+', [status(thm)], ['6', '15'])).
% 0.21/0.60  thf('17', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.60         ((k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.21/0.60           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.60           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.21/0.60              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.60      inference('demod', [status(thm)], ['5', '16'])).
% 0.21/0.60  thf(t62_enumset1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.60     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.60       ( k2_xboole_0 @
% 0.21/0.60         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.21/0.60  thf('18', plain,
% 0.21/0.60      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, 
% 0.21/0.60         X39 : $i]:
% 0.21/0.60         ((k6_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39)
% 0.21/0.60           = (k2_xboole_0 @ (k1_tarski @ X32) @ 
% 0.21/0.60              (k5_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t62_enumset1])).
% 0.21/0.60  thf('19', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.60         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.60           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.21/0.60              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.60      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.60  thf('20', plain,
% 0.21/0.60      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.21/0.60         != (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.21/0.60             sk_H))),
% 0.21/0.60      inference('demod', [status(thm)], ['0', '19'])).
% 0.21/0.60  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.21/0.60  
% 0.21/0.60  % SZS output end Refutation
% 0.21/0.60  
% 0.43/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
