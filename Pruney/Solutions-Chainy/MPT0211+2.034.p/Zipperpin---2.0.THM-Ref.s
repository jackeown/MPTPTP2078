%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8ml3816sZs

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  33 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :  238 ( 269 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :   10 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k2_tarski @ X11 @ X12 ) @ ( k2_tarski @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X20 @ X23 @ X21 @ X22 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('3',plain,(
    ( k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X35 @ X34 @ X33 @ X32 )
      = ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_enumset1 @ X57 @ X57 @ X58 @ X59 )
      = ( k1_enumset1 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X24 @ X27 @ X26 @ X25 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('8',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_enumset1 @ X57 @ X57 @ X58 @ X59 )
      = ( k1_enumset1 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X20 @ X23 @ X21 @ X22 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('11',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_enumset1 @ X57 @ X57 @ X58 @ X59 )
      = ( k1_enumset1 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['3','6','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8ml3816sZs
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 83 iterations in 0.131s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.57  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(t137_enumset1, conjecture,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.21/0.57       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.57        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.21/0.57          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.21/0.57         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(l53_enumset1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.57       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.57         ((k2_enumset1 @ X11 @ X12 @ X13 @ X14)
% 0.21/0.57           = (k2_xboole_0 @ (k2_tarski @ X11 @ X12) @ (k2_tarski @ X13 @ X14)))),
% 0.21/0.57      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.21/0.57  thf(t105_enumset1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.57         ((k2_enumset1 @ X20 @ X23 @ X21 @ X22)
% 0.21/0.57           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 0.21/0.57      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (((k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A)
% 0.21/0.57         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.21/0.57  thf(t125_enumset1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.57         ((k2_enumset1 @ X35 @ X34 @ X33 @ X32)
% 0.21/0.57           = (k2_enumset1 @ X32 @ X33 @ X34 @ X35))),
% 0.21/0.57      inference('cnf', [status(esa)], [t125_enumset1])).
% 0.21/0.57  thf(t71_enumset1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.21/0.57         ((k2_enumset1 @ X57 @ X57 @ X58 @ X59)
% 0.21/0.57           = (k1_enumset1 @ X57 @ X58 @ X59))),
% 0.21/0.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.21/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.57  thf(t107_enumset1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.57         ((k2_enumset1 @ X24 @ X27 @ X26 @ X25)
% 0.21/0.57           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 0.21/0.57      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.21/0.57         ((k2_enumset1 @ X57 @ X57 @ X58 @ X59)
% 0.21/0.57           = (k1_enumset1 @ X57 @ X58 @ X59))),
% 0.21/0.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.21/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.57         ((k2_enumset1 @ X20 @ X23 @ X21 @ X22)
% 0.21/0.57           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 0.21/0.57      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.21/0.57         ((k2_enumset1 @ X57 @ X57 @ X58 @ X59)
% 0.21/0.57           = (k1_enumset1 @ X57 @ X58 @ X59))),
% 0.21/0.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.21/0.57      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.21/0.57      inference('sup+', [status(thm)], ['9', '12'])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.21/0.57         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['3', '6', '13'])).
% 0.21/0.57  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
