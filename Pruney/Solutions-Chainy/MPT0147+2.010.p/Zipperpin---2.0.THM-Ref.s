%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sUvV5TRUcY

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:14 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :  260 ( 260 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

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

thf(t56_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X21 ) @ ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t56_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k6_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k1_tarski @ X28 ) @ ( k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t62_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sUvV5TRUcY
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:03:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 86 iterations in 0.175s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(sk_H_type, type, sk_H: $i).
% 0.46/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.46/0.63                                           $i > $i).
% 0.46/0.63  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.63  thf(sk_E_type, type, sk_E: $i).
% 0.46/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.63  thf(sk_F_type, type, sk_F: $i).
% 0.46/0.63  thf(sk_G_type, type, sk_G: $i).
% 0.46/0.63  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.63  thf(t63_enumset1, conjecture,
% 0.46/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.46/0.63     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.46/0.63       ( k2_xboole_0 @
% 0.46/0.63         ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.46/0.63        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.46/0.63          ( k2_xboole_0 @
% 0.46/0.63            ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t63_enumset1])).
% 0.46/0.63  thf('0', plain,
% 0.46/0.63      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.46/0.63         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.46/0.63             (k4_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t56_enumset1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.46/0.63     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.46/0.63       ( k2_xboole_0 @
% 0.46/0.63         ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ))).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.63         ((k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.46/0.63           = (k2_xboole_0 @ (k1_tarski @ X21) @ 
% 0.46/0.63              (k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t56_enumset1])).
% 0.46/0.63  thf(t41_enumset1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( k2_tarski @ A @ B ) =
% 0.46/0.63       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (![X10 : $i, X11 : $i]:
% 0.46/0.63         ((k2_tarski @ X10 @ X11)
% 0.46/0.63           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_tarski @ X11)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.46/0.63  thf(t4_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.63       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.63  thf('3', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.63         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 0.46/0.63           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.46/0.63           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.46/0.63              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['2', '3'])).
% 0.46/0.63  thf('5', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.63         ((k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.46/0.63           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.46/0.63           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.46/0.63              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['1', '4'])).
% 0.46/0.63  thf(t62_enumset1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.46/0.63     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.46/0.63       ( k2_xboole_0 @
% 0.46/0.63         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.46/0.63  thf('6', plain,
% 0.46/0.63      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, 
% 0.46/0.63         X35 : $i]:
% 0.46/0.63         ((k6_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)
% 0.46/0.63           = (k2_xboole_0 @ (k1_tarski @ X28) @ 
% 0.46/0.63              (k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t62_enumset1])).
% 0.46/0.63  thf('7', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.63         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.46/0.63           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.46/0.63              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['5', '6'])).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.46/0.63         != (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.46/0.63             sk_H))),
% 0.46/0.63      inference('demod', [status(thm)], ['0', '7'])).
% 0.46/0.63  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
