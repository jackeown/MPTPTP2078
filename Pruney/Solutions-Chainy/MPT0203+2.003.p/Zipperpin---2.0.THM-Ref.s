%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MLoVAjEPj2

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:26 EST 2020

% Result     : Theorem 13.20s
% Output     : Refutation 13.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  43 expanded)
%              Number of leaves         :   24 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  437 ( 449 expanded)
%              Number of equality atoms :   25 (  26 expanded)
%              Maximal formula depth    :   21 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k7_enumset1_type,type,(
    k7_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t129_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k4_enumset1 @ D @ E @ F @ G @ H @ I ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
        ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
        = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k4_enumset1 @ D @ E @ F @ G @ H @ I ) ) ) ),
    inference('cnf.neg',[status(esa)],[t129_enumset1])).

thf('0',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k2_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) @ ( k4_enumset1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('1',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k3_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k3_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k4_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('6',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k4_enumset1 @ X33 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k3_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X9 @ X8 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X9 @ X8 @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k3_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X3 @ X2 @ X1 ) @ ( k4_enumset1 @ X0 @ X8 @ X7 @ X6 @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf(l142_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k3_enumset1 @ E @ F @ G @ H @ I ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k7_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 ) @ ( k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l142_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('13',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k2_enumset1 @ X26 @ X26 @ X27 @ X28 )
      = ( k1_enumset1 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k7_enumset1 @ X3 @ X2 @ X1 @ X0 @ X8 @ X7 @ X6 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k4_enumset1 @ X0 @ X8 @ X7 @ X6 @ X5 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(demod,[status(thm)],['0','14'])).

thf('16',plain,(
    $false ),
    inference(simplify,[status(thm)],['15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MLoVAjEPj2
% 0.17/0.38  % Computer   : n019.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 13:24:38 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.39  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 13.20/13.41  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 13.20/13.41  % Solved by: fo/fo7.sh
% 13.20/13.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.20/13.41  % done 9378 iterations in 12.915s
% 13.20/13.41  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 13.20/13.41  % SZS output start Refutation
% 13.20/13.41  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 13.20/13.41  thf(k7_enumset1_type, type, k7_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 13.20/13.41                                           $i > $i > $i).
% 13.20/13.41  thf(sk_A_type, type, sk_A: $i).
% 13.20/13.41  thf(sk_G_type, type, sk_G: $i).
% 13.20/13.41  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 13.20/13.41  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 13.20/13.41  thf(sk_C_type, type, sk_C: $i).
% 13.20/13.41  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 13.20/13.41  thf(sk_H_type, type, sk_H: $i).
% 13.20/13.41  thf(sk_D_type, type, sk_D: $i).
% 13.20/13.41  thf(sk_I_type, type, sk_I: $i).
% 13.20/13.41  thf(sk_B_type, type, sk_B: $i).
% 13.20/13.41  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 13.20/13.41  thf(sk_E_type, type, sk_E: $i).
% 13.20/13.41  thf(sk_F_type, type, sk_F: $i).
% 13.20/13.41  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 13.20/13.41  thf(t129_enumset1, conjecture,
% 13.20/13.41    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 13.20/13.41     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 13.20/13.41       ( k2_xboole_0 @
% 13.20/13.41         ( k1_enumset1 @ A @ B @ C ) @ ( k4_enumset1 @ D @ E @ F @ G @ H @ I ) ) ))).
% 13.20/13.41  thf(zf_stmt_0, negated_conjecture,
% 13.20/13.41    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 13.20/13.41        ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 13.20/13.41          ( k2_xboole_0 @
% 13.20/13.41            ( k1_enumset1 @ A @ B @ C ) @ 
% 13.20/13.41            ( k4_enumset1 @ D @ E @ F @ G @ H @ I ) ) ) )),
% 13.20/13.41    inference('cnf.neg', [status(esa)], [t129_enumset1])).
% 13.20/13.41  thf('0', plain,
% 13.20/13.41      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 13.20/13.41         sk_I)
% 13.20/13.41         != (k2_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_C) @ 
% 13.20/13.41             (k4_enumset1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I)))),
% 13.20/13.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.20/13.41  thf(t72_enumset1, axiom,
% 13.20/13.41    (![A:$i,B:$i,C:$i,D:$i]:
% 13.20/13.41     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 13.20/13.41  thf('1', plain,
% 13.20/13.41      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 13.20/13.41         ((k3_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32)
% 13.20/13.41           = (k2_enumset1 @ X29 @ X30 @ X31 @ X32))),
% 13.20/13.41      inference('cnf', [status(esa)], [t72_enumset1])).
% 13.20/13.41  thf(t51_enumset1, axiom,
% 13.20/13.41    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 13.20/13.41     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 13.20/13.41       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 13.20/13.41  thf('2', plain,
% 13.20/13.41      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 13.20/13.41         ((k4_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19)
% 13.20/13.41           = (k2_xboole_0 @ (k1_tarski @ X14) @ 
% 13.20/13.41              (k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19)))),
% 13.20/13.41      inference('cnf', [status(esa)], [t51_enumset1])).
% 13.20/13.41  thf('3', plain,
% 13.20/13.41      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 13.20/13.41         ((k3_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32)
% 13.20/13.41           = (k2_enumset1 @ X29 @ X30 @ X31 @ X32))),
% 13.20/13.41      inference('cnf', [status(esa)], [t72_enumset1])).
% 13.20/13.41  thf(t55_enumset1, axiom,
% 13.20/13.41    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 13.20/13.41     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 13.20/13.41       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 13.20/13.41  thf('4', plain,
% 13.20/13.41      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 13.20/13.41         ((k4_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25)
% 13.20/13.41           = (k2_xboole_0 @ (k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24) @ 
% 13.20/13.41              (k1_tarski @ X25)))),
% 13.20/13.41      inference('cnf', [status(esa)], [t55_enumset1])).
% 13.20/13.41  thf('5', plain,
% 13.20/13.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.20/13.41         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.20/13.41           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.20/13.41              (k1_tarski @ X4)))),
% 13.20/13.41      inference('sup+', [status(thm)], ['3', '4'])).
% 13.20/13.41  thf(t73_enumset1, axiom,
% 13.20/13.41    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 13.20/13.41     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 13.20/13.41       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 13.20/13.41  thf('6', plain,
% 13.20/13.41      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 13.20/13.41         ((k4_enumset1 @ X33 @ X33 @ X34 @ X35 @ X36 @ X37)
% 13.20/13.41           = (k3_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37))),
% 13.20/13.41      inference('cnf', [status(esa)], [t73_enumset1])).
% 13.20/13.41  thf('7', plain,
% 13.20/13.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.20/13.41         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 13.20/13.41           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.20/13.41              (k1_tarski @ X4)))),
% 13.20/13.41      inference('demod', [status(thm)], ['5', '6'])).
% 13.20/13.41  thf(t4_xboole_1, axiom,
% 13.20/13.41    (![A:$i,B:$i,C:$i]:
% 13.20/13.41     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 13.20/13.41       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 13.20/13.41  thf('8', plain,
% 13.20/13.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.20/13.41         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 13.20/13.41           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 13.20/13.41      inference('cnf', [status(esa)], [t4_xboole_1])).
% 13.20/13.41  thf('9', plain,
% 13.20/13.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 13.20/13.41         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 13.20/13.41           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 13.20/13.41              (k2_xboole_0 @ (k1_tarski @ X0) @ X5)))),
% 13.20/13.41      inference('sup+', [status(thm)], ['7', '8'])).
% 13.20/13.41  thf('10', plain,
% 13.20/13.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 13.20/13.41         X7 : $i, X8 : $i, X9 : $i]:
% 13.20/13.41         ((k2_xboole_0 @ (k3_enumset1 @ X9 @ X8 @ X7 @ X6 @ X5) @ 
% 13.20/13.41           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 13.20/13.41           = (k2_xboole_0 @ (k2_enumset1 @ X9 @ X8 @ X7 @ X6) @ 
% 13.20/13.41              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 13.20/13.41      inference('sup+', [status(thm)], ['2', '9'])).
% 13.20/13.41  thf('11', plain,
% 13.20/13.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 13.20/13.41         X7 : $i, X8 : $i]:
% 13.20/13.41         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.20/13.41           (k3_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4))
% 13.20/13.41           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X3 @ X2 @ X1) @ 
% 13.20/13.41              (k4_enumset1 @ X0 @ X8 @ X7 @ X6 @ X5 @ X4)))),
% 13.20/13.41      inference('sup+', [status(thm)], ['1', '10'])).
% 13.20/13.41  thf(l142_enumset1, axiom,
% 13.20/13.41    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 13.20/13.41     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 13.20/13.41       ( k2_xboole_0 @
% 13.20/13.41         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k3_enumset1 @ E @ F @ G @ H @ I ) ) ))).
% 13.20/13.41  thf('12', plain,
% 13.20/13.41      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, 
% 13.20/13.41         X12 : $i, X13 : $i]:
% 13.20/13.41         ((k7_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 13.20/13.41           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X6 @ X7 @ X8) @ 
% 13.20/13.41              (k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13)))),
% 13.20/13.41      inference('cnf', [status(esa)], [l142_enumset1])).
% 13.20/13.41  thf(t71_enumset1, axiom,
% 13.20/13.41    (![A:$i,B:$i,C:$i]:
% 13.20/13.41     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 13.20/13.41  thf('13', plain,
% 13.20/13.41      (![X26 : $i, X27 : $i, X28 : $i]:
% 13.20/13.41         ((k2_enumset1 @ X26 @ X26 @ X27 @ X28)
% 13.20/13.41           = (k1_enumset1 @ X26 @ X27 @ X28))),
% 13.20/13.41      inference('cnf', [status(esa)], [t71_enumset1])).
% 13.20/13.41  thf('14', plain,
% 13.20/13.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 13.20/13.41         X7 : $i, X8 : $i]:
% 13.20/13.41         ((k7_enumset1 @ X3 @ X2 @ X1 @ X0 @ X8 @ X7 @ X6 @ X5 @ X4)
% 13.20/13.41           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ 
% 13.20/13.41              (k4_enumset1 @ X0 @ X8 @ X7 @ X6 @ X5 @ X4)))),
% 13.20/13.41      inference('demod', [status(thm)], ['11', '12', '13'])).
% 13.20/13.41  thf('15', plain,
% 13.20/13.41      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 13.20/13.41         sk_I)
% 13.20/13.41         != (k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 13.20/13.41             sk_H @ sk_I))),
% 13.20/13.41      inference('demod', [status(thm)], ['0', '14'])).
% 13.20/13.41  thf('16', plain, ($false), inference('simplify', [status(thm)], ['15'])).
% 13.20/13.41  
% 13.20/13.41  % SZS output end Refutation
% 13.20/13.41  
% 13.20/13.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
