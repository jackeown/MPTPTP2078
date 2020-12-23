%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Lj6yJUXKzf

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   16 (  17 expanded)
%              Number of leaves         :    8 (   9 expanded)
%              Depth                    :    5
%              Number of atoms          :  111 ( 122 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t116_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ B @ A @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ C @ B @ A @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t116_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_C @ sk_B @ sk_A @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('2',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_C @ sk_A @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t108_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ A @ C @ D ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X5 @ X4 @ X6 @ X7 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t108_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('5',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    $false ),
    inference(simplify,[status(thm)],['5'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Lj6yJUXKzf
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 3 iterations in 0.012s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(t116_enumset1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ B @ A @ D ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ B @ A @ D ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t116_enumset1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.49         != (k2_enumset1 @ sk_C @ sk_B @ sk_A @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t105_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.49         != (k2_enumset1 @ sk_C @ sk_A @ sk_D @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(t108_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         ((k2_enumset1 @ X5 @ X4 @ X6 @ X7) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t108_enumset1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.49         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.21/0.49  thf('6', plain, ($false), inference('simplify', [status(thm)], ['5'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
