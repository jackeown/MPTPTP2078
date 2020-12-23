%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XfKMcucOpn

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:04 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  217 ( 244 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(t104_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ A @ C @ B @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t104_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X8 ) @ ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X8 ) @ ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X0 @ X2 @ X1 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t103_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ D @ C ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X3 @ X4 @ X6 @ X5 )
      = ( k2_enumset1 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('11',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','9','10'])).

thf('12',plain,(
    $false ),
    inference(simplify,[status(thm)],['11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XfKMcucOpn
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.62/0.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.62/0.82  % Solved by: fo/fo7.sh
% 0.62/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.82  % done 829 iterations in 0.374s
% 0.62/0.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.62/0.82  % SZS output start Refutation
% 0.62/0.82  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.62/0.82  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.62/0.82  thf(sk_D_type, type, sk_D: $i).
% 0.62/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.82  thf(sk_C_type, type, sk_C: $i).
% 0.62/0.82  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.62/0.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.62/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.82  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.62/0.82  thf(t104_enumset1, conjecture,
% 0.62/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.82     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 0.62/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.82    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.82        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ) )),
% 0.62/0.82    inference('cnf.neg', [status(esa)], [t104_enumset1])).
% 0.62/0.82  thf('0', plain,
% 0.62/0.82      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.62/0.82         != (k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D))),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf(t100_enumset1, axiom,
% 0.62/0.82    (![A:$i,B:$i,C:$i]:
% 0.62/0.82     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 0.62/0.82  thf('1', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.82         ((k1_enumset1 @ X2 @ X0 @ X1) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.62/0.82      inference('cnf', [status(esa)], [t100_enumset1])).
% 0.62/0.82  thf(t48_enumset1, axiom,
% 0.62/0.82    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.62/0.82     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.62/0.82       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.62/0.82  thf('2', plain,
% 0.62/0.82      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.62/0.82         ((k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11)
% 0.62/0.82           = (k2_xboole_0 @ (k2_tarski @ X7 @ X8) @ 
% 0.62/0.82              (k1_enumset1 @ X9 @ X10 @ X11)))),
% 0.62/0.82      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.62/0.82  thf('3', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.62/0.82         ((k3_enumset1 @ X4 @ X3 @ X1 @ X0 @ X2)
% 0.62/0.82           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.62/0.82              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.62/0.82      inference('sup+', [status(thm)], ['1', '2'])).
% 0.62/0.82  thf('4', plain,
% 0.62/0.82      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.62/0.82         ((k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11)
% 0.62/0.82           = (k2_xboole_0 @ (k2_tarski @ X7 @ X8) @ 
% 0.62/0.82              (k1_enumset1 @ X9 @ X10 @ X11)))),
% 0.62/0.82      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.62/0.82  thf('5', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.62/0.82         ((k3_enumset1 @ X4 @ X3 @ X0 @ X2 @ X1)
% 0.62/0.82           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.62/0.82      inference('sup+', [status(thm)], ['3', '4'])).
% 0.62/0.82  thf(t72_enumset1, axiom,
% 0.62/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.82     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.62/0.82  thf('6', plain,
% 0.62/0.82      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.62/0.82         ((k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20)
% 0.62/0.82           = (k2_enumset1 @ X17 @ X18 @ X19 @ X20))),
% 0.62/0.82      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.62/0.82  thf('7', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.62/0.82         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.62/0.82           = (k2_enumset1 @ X3 @ X1 @ X0 @ X2))),
% 0.62/0.82      inference('sup+', [status(thm)], ['5', '6'])).
% 0.62/0.82  thf('8', plain,
% 0.62/0.82      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.62/0.82         ((k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20)
% 0.62/0.82           = (k2_enumset1 @ X17 @ X18 @ X19 @ X20))),
% 0.62/0.82      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.62/0.82  thf('9', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.62/0.82         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X0 @ X2 @ X1))),
% 0.62/0.82      inference('sup+', [status(thm)], ['7', '8'])).
% 0.62/0.82  thf(t103_enumset1, axiom,
% 0.62/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.82     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 0.62/0.82  thf('10', plain,
% 0.62/0.82      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.62/0.82         ((k2_enumset1 @ X3 @ X4 @ X6 @ X5) = (k2_enumset1 @ X3 @ X4 @ X5 @ X6))),
% 0.62/0.82      inference('cnf', [status(esa)], [t103_enumset1])).
% 0.62/0.82  thf('11', plain,
% 0.62/0.82      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.62/0.82         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.62/0.82      inference('demod', [status(thm)], ['0', '9', '10'])).
% 0.62/0.82  thf('12', plain, ($false), inference('simplify', [status(thm)], ['11'])).
% 0.62/0.82  
% 0.62/0.82  % SZS output end Refutation
% 0.62/0.82  
% 0.66/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
