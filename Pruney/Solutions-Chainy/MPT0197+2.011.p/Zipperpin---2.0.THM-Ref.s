%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gdnvYX5weH

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:20 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   13 (  14 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    4
%              Number of atoms          :   78 (  89 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t118_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ D @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ C @ D @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t118_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_C @ sk_D @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t111_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ C @ D @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t111_enumset1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t111_enumset1])).

thf('3',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    $false ),
    inference(simplify,[status(thm)],['3'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gdnvYX5weH
% 0.14/0.37  % Computer   : n001.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 12:59:30 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.23/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.48  % Solved by: fo/fo7.sh
% 0.23/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.48  % done 1 iterations in 0.008s
% 0.23/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.48  % SZS output start Refutation
% 0.23/0.48  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.23/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.48  thf(t118_enumset1, conjecture,
% 0.23/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.48     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ D @ A @ B ) ))).
% 0.23/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.48        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ D @ A @ B ) ) )),
% 0.23/0.48    inference('cnf.neg', [status(esa)], [t118_enumset1])).
% 0.23/0.48  thf('0', plain,
% 0.23/0.48      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.23/0.48         != (k2_enumset1 @ sk_C @ sk_D @ sk_A @ sk_B))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(t111_enumset1, axiom,
% 0.23/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.48     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ C @ D @ A ) ))).
% 0.23/0.48  thf('1', plain,
% 0.23/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.48         ((k2_enumset1 @ X3 @ X0 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.23/0.48      inference('cnf', [status(esa)], [t111_enumset1])).
% 0.23/0.48  thf('2', plain,
% 0.23/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.48         ((k2_enumset1 @ X3 @ X0 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.23/0.48      inference('cnf', [status(esa)], [t111_enumset1])).
% 0.23/0.48  thf('3', plain,
% 0.23/0.48      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.23/0.48         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.23/0.48      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.23/0.48  thf('4', plain, ($false), inference('simplify', [status(thm)], ['3'])).
% 0.23/0.48  
% 0.23/0.48  % SZS output end Refutation
% 0.23/0.48  
% 0.23/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
