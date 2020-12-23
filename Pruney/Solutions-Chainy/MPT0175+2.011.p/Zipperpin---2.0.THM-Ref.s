%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lxZH10i3Ox

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:51 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    4
%              Number of atoms          :   82 (  82 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t91_enumset1,conjecture,(
    ! [A: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k4_enumset1 @ A @ A @ A @ A @ A @ A )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t91_enumset1])).

thf('0',plain,(
    ( k4_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t87_enumset1,axiom,(
    ! [A: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( k3_enumset1 @ X5 @ X5 @ X5 @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t87_enumset1])).

thf('3',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    $false ),
    inference(simplify,[status(thm)],['3'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lxZH10i3Ox
% 0.16/0.38  % Computer   : n023.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 20:36:51 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.25/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.50  % Solved by: fo/fo7.sh
% 0.25/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.50  % done 2 iterations in 0.006s
% 0.25/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.50  % SZS output start Refutation
% 0.25/0.50  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.25/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.50  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.25/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.25/0.50  thf(t91_enumset1, conjecture,
% 0.25/0.50    (![A:$i]: ( ( k4_enumset1 @ A @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.25/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.50    (~( ![A:$i]:
% 0.25/0.50        ( ( k4_enumset1 @ A @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ) )),
% 0.25/0.50    inference('cnf.neg', [status(esa)], [t91_enumset1])).
% 0.25/0.50  thf('0', plain,
% 0.25/0.50      (((k4_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.25/0.50         != (k1_tarski @ sk_A))),
% 0.25/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.50  thf(t73_enumset1, axiom,
% 0.25/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.25/0.50     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.25/0.50       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.25/0.50  thf('1', plain,
% 0.25/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.25/0.50         ((k4_enumset1 @ X0 @ X0 @ X1 @ X2 @ X3 @ X4)
% 0.25/0.50           = (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.25/0.50      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.25/0.50  thf(t87_enumset1, axiom,
% 0.25/0.50    (![A:$i]: ( ( k3_enumset1 @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.25/0.50  thf('2', plain,
% 0.25/0.50      (![X5 : $i]: ((k3_enumset1 @ X5 @ X5 @ X5 @ X5 @ X5) = (k1_tarski @ X5))),
% 0.25/0.50      inference('cnf', [status(esa)], [t87_enumset1])).
% 0.25/0.50  thf('3', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.25/0.50      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.25/0.50  thf('4', plain, ($false), inference('simplify', [status(thm)], ['3'])).
% 0.25/0.50  
% 0.25/0.50  % SZS output end Refutation
% 0.25/0.50  
% 0.25/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
