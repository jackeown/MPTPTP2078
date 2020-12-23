%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cWyjawqVVR

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  34 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  253 ( 268 expanded)
%              Number of equality atoms :   20 (  21 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t73_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) ),
    inference('cnf.neg',[status(esa)],[t73_enumset1])).

thf('0',plain,(
    ( k4_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k3_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k2_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k3_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['0','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cWyjawqVVR
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:45:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 125 iterations in 0.075s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.54  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.54  thf(t73_enumset1, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.54     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.20/0.54       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.54        ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.20/0.54          ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t73_enumset1])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (((k4_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.54         != (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t47_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.54     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.20/0.54       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.54         ((k3_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X8) @ 
% 0.20/0.54              (k2_enumset1 @ X9 @ X10 @ X11 @ X12)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.20/0.54  thf(d10_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.54  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.54  thf(t12_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.20/0.54      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.54  thf('5', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.54  thf(t4_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.54       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X7)
% 0.20/0.54           = (k2_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ X0 @ X1)
% 0.20/0.54           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k1_tarski @ X4) @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.20/0.54              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['1', '7'])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.54         ((k3_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X8) @ 
% 0.20/0.54              (k2_enumset1 @ X9 @ X10 @ X11 @ X12)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.20/0.54              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf(t51_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.54     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.20/0.54       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.54         ((k4_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X13) @ 
% 0.20/0.54              (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.54           = (k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.54         != (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.20/0.54      inference('demod', [status(thm)], ['0', '12'])).
% 0.20/0.54  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
