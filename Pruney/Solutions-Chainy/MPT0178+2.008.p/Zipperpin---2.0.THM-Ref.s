%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s7391EdoQ6

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:54 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    4
%              Number of atoms          :  131 ( 131 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t94_enumset1,conjecture,(
    ! [A: $i] :
      ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ A )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t94_enumset1])).

thf('0',plain,(
    ( k5_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k4_enumset1 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t79_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_enumset1 @ X10 @ X10 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t79_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t76_enumset1,axiom,(
    ! [A: $i] :
      ( ( k1_enumset1 @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X9: $i] :
      ( ( k1_enumset1 @ X9 @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf('5',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2','3','4'])).

thf('6',plain,(
    $false ),
    inference(simplify,[status(thm)],['5'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s7391EdoQ6
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 4 iterations in 0.008s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.46  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.19/0.46  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.19/0.46  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.46  thf(t94_enumset1, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t94_enumset1])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (((k5_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.19/0.46         != (k1_tarski @ sk_A))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t74_enumset1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.46     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.19/0.46       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.46         ((k5_enumset1 @ X3 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8)
% 0.19/0.46           = (k4_enumset1 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8))),
% 0.19/0.46      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.19/0.46  thf(t79_enumset1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46     ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D ) =
% 0.19/0.46       ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.46         ((k4_enumset1 @ X10 @ X10 @ X10 @ X11 @ X12 @ X13)
% 0.19/0.46           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.19/0.46      inference('cnf', [status(esa)], [t79_enumset1])).
% 0.19/0.46  thf(t71_enumset1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         ((k2_enumset1 @ X0 @ X0 @ X1 @ X2) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.19/0.46      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.19/0.46  thf(t76_enumset1, axiom,
% 0.19/0.46    (![A:$i]: ( ( k1_enumset1 @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X9 : $i]: ((k1_enumset1 @ X9 @ X9 @ X9) = (k1_tarski @ X9))),
% 0.19/0.46      inference('cnf', [status(esa)], [t76_enumset1])).
% 0.19/0.46  thf('5', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['0', '1', '2', '3', '4'])).
% 0.19/0.46  thf('6', plain, ($false), inference('simplify', [status(thm)], ['5'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
