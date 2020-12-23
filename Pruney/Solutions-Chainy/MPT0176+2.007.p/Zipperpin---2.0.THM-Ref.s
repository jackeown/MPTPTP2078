%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GH0zJNyhKr

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    4
%              Number of atoms          :  116 ( 116 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(t92_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ B )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t92_enumset1])).

thf('0',plain,(
    ( k5_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k5_enumset1 @ X2 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 )
      = ( k4_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t84_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_enumset1 @ X8 @ X8 @ X8 @ X8 @ X9 @ X10 )
      = ( k1_enumset1 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t84_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('4',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1','2','3'])).

thf('5',plain,(
    $false ),
    inference(simplify,[status(thm)],['4'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GH0zJNyhKr
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:27:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 3 iterations in 0.007s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.51  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.22/0.51  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.22/0.51  thf(t92_enumset1, conjecture,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i]:
% 0.22/0.51        ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t92_enumset1])).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (((k5_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B)
% 0.22/0.51         != (k2_tarski @ sk_A @ sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t74_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.51     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.22/0.51       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.51         ((k5_enumset1 @ X2 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7)
% 0.22/0.51           = (k4_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.22/0.51  thf(t84_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( k4_enumset1 @ A @ A @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.51         ((k4_enumset1 @ X8 @ X8 @ X8 @ X8 @ X9 @ X10)
% 0.22/0.51           = (k1_enumset1 @ X8 @ X9 @ X10))),
% 0.22/0.51      inference('cnf', [status(esa)], [t84_enumset1])).
% 0.22/0.51  thf(t70_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.51  thf('4', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['0', '1', '2', '3'])).
% 0.22/0.51  thf('5', plain, ($false), inference('simplify', [status(thm)], ['4'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
