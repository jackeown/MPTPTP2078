%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ausg6eJrMM

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:02 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   19 (  20 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :  122 ( 135 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t103_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ D @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ A @ B @ D @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t103_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    $false ),
    inference(simplify,[status(thm)],['6'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ausg6eJrMM
% 0.16/0.37  % Computer   : n023.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 19:12:51 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.24/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.51  % Solved by: fo/fo7.sh
% 0.24/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.51  % done 32 iterations in 0.023s
% 0.24/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.51  % SZS output start Refutation
% 0.24/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.51  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.24/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.24/0.51  thf(t103_enumset1, conjecture,
% 0.24/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.51     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 0.24/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.51        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ) )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t103_enumset1])).
% 0.24/0.51  thf('0', plain,
% 0.24/0.51      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.24/0.51         != (k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(commutativity_k2_tarski, axiom,
% 0.24/0.51    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.24/0.51  thf('1', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.24/0.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.24/0.51  thf(l53_enumset1, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.51     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.24/0.51       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.24/0.51  thf('2', plain,
% 0.24/0.51      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.24/0.51         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 0.24/0.51           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 0.24/0.51      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.24/0.51  thf('3', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.51         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1)
% 0.24/0.51           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.24/0.51      inference('sup+', [status(thm)], ['1', '2'])).
% 0.24/0.51  thf('4', plain,
% 0.24/0.51      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.24/0.51         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 0.24/0.51           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 0.24/0.51      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.24/0.51  thf('5', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.51         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.24/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.24/0.51  thf('6', plain,
% 0.24/0.51      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.24/0.51         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.24/0.51      inference('demod', [status(thm)], ['0', '5'])).
% 0.24/0.51  thf('7', plain, ($false), inference('simplify', [status(thm)], ['6'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
