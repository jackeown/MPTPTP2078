%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UZZvEoNW3e

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:20 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    5
%              Number of atoms          :  100 ( 100 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('2',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_C @ sk_B @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t116_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ B @ A @ D ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X6 @ X5 @ X4 @ X7 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t116_enumset1])).

thf('4',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    $false ),
    inference(simplify,[status(thm)],['4'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UZZvEoNW3e
% 0.16/0.38  % Computer   : n025.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 14:22:21 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.25/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.50  % Solved by: fo/fo7.sh
% 0.25/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.50  % done 3 iterations in 0.010s
% 0.25/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.50  % SZS output start Refutation
% 0.25/0.50  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.25/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.25/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.25/0.50  thf(t118_enumset1, conjecture,
% 0.25/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.50     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ D @ A @ B ) ))).
% 0.25/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.50        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ D @ A @ B ) ) )),
% 0.25/0.50    inference('cnf.neg', [status(esa)], [t118_enumset1])).
% 0.25/0.50  thf('0', plain,
% 0.25/0.50      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.25/0.50         != (k2_enumset1 @ sk_C @ sk_D @ sk_A @ sk_B))),
% 0.25/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.50  thf(t107_enumset1, axiom,
% 0.25/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.50     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 0.25/0.50  thf('1', plain,
% 0.25/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.50         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.25/0.50      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.25/0.50  thf('2', plain,
% 0.25/0.50      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.25/0.50         != (k2_enumset1 @ sk_C @ sk_B @ sk_A @ sk_D))),
% 0.25/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.25/0.50  thf(t116_enumset1, axiom,
% 0.25/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.50     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ B @ A @ D ) ))).
% 0.25/0.50  thf('3', plain,
% 0.25/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.25/0.50         ((k2_enumset1 @ X6 @ X5 @ X4 @ X7) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.25/0.50      inference('cnf', [status(esa)], [t116_enumset1])).
% 0.25/0.50  thf('4', plain,
% 0.25/0.50      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.25/0.50         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.25/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.25/0.50  thf('5', plain, ($false), inference('simplify', [status(thm)], ['4'])).
% 0.25/0.50  
% 0.25/0.50  % SZS output end Refutation
% 0.25/0.50  
% 0.25/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
