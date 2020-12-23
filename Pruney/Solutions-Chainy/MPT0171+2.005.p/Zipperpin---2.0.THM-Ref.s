%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ng6RBWLYYU

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    4
%              Number of atoms          :  105 ( 105 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(t87_enumset1,conjecture,(
    ! [A: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k3_enumset1 @ A @ A @ A @ A @ A )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t87_enumset1])).

thf('0',plain,(
    ( k3_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('5',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2','3','4'])).

thf('6',plain,(
    $false ),
    inference(simplify,[status(thm)],['5'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ng6RBWLYYU
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:59:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 4 iterations in 0.007s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.47  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.22/0.47  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.22/0.47  thf(t87_enumset1, conjecture,
% 0.22/0.47    (![A:$i]: ( ( k3_enumset1 @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i]: ( ( k3_enumset1 @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t87_enumset1])).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      (((k3_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_tarski @ sk_A))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(t72_enumset1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.47     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.47         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.22/0.47           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.22/0.47      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.22/0.47  thf(t71_enumset1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.47         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.22/0.47      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.22/0.47  thf(t70_enumset1, axiom,
% 0.22/0.47    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X1 : $i, X2 : $i]:
% 0.22/0.47         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.22/0.47      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.47  thf(t69_enumset1, axiom,
% 0.22/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.47  thf('4', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.22/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.47  thf('5', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['0', '1', '2', '3', '4'])).
% 0.22/0.47  thf('6', plain, ($false), inference('simplify', [status(thm)], ['5'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
