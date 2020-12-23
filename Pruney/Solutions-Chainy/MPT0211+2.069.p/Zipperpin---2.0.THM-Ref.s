%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iJf5wrgQR7

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:39 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   31 (  36 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :  243 ( 295 expanded)
%              Number of equality atoms :   22 (  27 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k3_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t113_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ C @ A ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X18 @ X15 @ X17 @ X16 )
      = ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k2_enumset1 @ X26 @ X26 @ X27 @ X28 )
      = ( k1_enumset1 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t112_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ A @ C ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X13 @ X11 @ X14 @ X12 )
      = ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t112_enumset1])).

thf('10',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k2_enumset1 @ X26 @ X26 @ X27 @ X28 )
      = ( k1_enumset1 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','3','4','7','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iJf5wrgQR7
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 334 iterations in 0.200s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.65  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.45/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.65  thf(t137_enumset1, conjecture,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.45/0.65       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.65        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.45/0.65          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.45/0.65         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t70_enumset1, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (![X24 : $i, X25 : $i]:
% 0.45/0.65         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.45/0.65      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.65  thf(l57_enumset1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.45/0.65     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.45/0.65       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.65         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.45/0.65           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 0.45/0.65              (k2_tarski @ X5 @ X6)))),
% 0.45/0.65      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.65         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 0.45/0.65           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['1', '2'])).
% 0.45/0.65  thf(t72_enumset1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.45/0.65         ((k3_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32)
% 0.45/0.65           = (k2_enumset1 @ X29 @ X30 @ X31 @ X32))),
% 0.45/0.65      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.45/0.65  thf(t113_enumset1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ C @ A ) ))).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.65         ((k2_enumset1 @ X18 @ X15 @ X17 @ X16)
% 0.45/0.65           = (k2_enumset1 @ X15 @ X16 @ X17 @ X18))),
% 0.45/0.65      inference('cnf', [status(esa)], [t113_enumset1])).
% 0.45/0.65  thf(t71_enumset1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.65         ((k2_enumset1 @ X26 @ X26 @ X27 @ X28)
% 0.45/0.65           = (k1_enumset1 @ X26 @ X27 @ X28))),
% 0.45/0.65      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.45/0.65      inference('sup+', [status(thm)], ['5', '6'])).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.45/0.65      inference('sup+', [status(thm)], ['5', '6'])).
% 0.45/0.65  thf(t112_enumset1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ A @ C ) ))).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.65         ((k2_enumset1 @ X13 @ X11 @ X14 @ X12)
% 0.45/0.65           = (k2_enumset1 @ X11 @ X12 @ X13 @ X14))),
% 0.45/0.65      inference('cnf', [status(esa)], [t112_enumset1])).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.65         ((k2_enumset1 @ X26 @ X26 @ X27 @ X28)
% 0.45/0.65           = (k1_enumset1 @ X26 @ X27 @ X28))),
% 0.45/0.65      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.45/0.65      inference('sup+', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.45/0.65      inference('sup+', [status(thm)], ['8', '11'])).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.45/0.65         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.45/0.65      inference('demod', [status(thm)], ['0', '3', '4', '7', '12'])).
% 0.45/0.65  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
