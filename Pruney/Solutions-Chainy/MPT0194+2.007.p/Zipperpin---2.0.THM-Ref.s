%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AgvyhWRxU6

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:15 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   17 (  22 expanded)
%              Number of leaves         :    8 (  11 expanded)
%              Depth                    :    4
%              Number of atoms          :  122 ( 177 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t113_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ C @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ B @ D @ C @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t113_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_B @ sk_D @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t112_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ A @ C ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X6 @ X4 @ X7 @ X5 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t112_enumset1])).

thf(l123_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ C @ A @ D ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X3 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l123_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X3 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l123_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('6',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','3','4','5'])).

thf('7',plain,(
    $false ),
    inference(simplify,[status(thm)],['6'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AgvyhWRxU6
% 0.13/0.36  % Computer   : n024.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 15:47:06 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.23/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.45  % Solved by: fo/fo7.sh
% 0.23/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.45  % done 9 iterations in 0.010s
% 0.23/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.45  % SZS output start Refutation
% 0.23/0.45  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.23/0.45  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.45  thf(t113_enumset1, conjecture,
% 0.23/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.45     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ C @ A ) ))).
% 0.23/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.45    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.45        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ C @ A ) ) )),
% 0.23/0.45    inference('cnf.neg', [status(esa)], [t113_enumset1])).
% 0.23/0.45  thf('0', plain,
% 0.23/0.45      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.23/0.45         != (k2_enumset1 @ sk_B @ sk_D @ sk_C @ sk_A))),
% 0.23/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.45  thf(t112_enumset1, axiom,
% 0.23/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.45     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ A @ C ) ))).
% 0.23/0.45  thf('1', plain,
% 0.23/0.45      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.45         ((k2_enumset1 @ X6 @ X4 @ X7 @ X5) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.23/0.45      inference('cnf', [status(esa)], [t112_enumset1])).
% 0.23/0.45  thf(l123_enumset1, axiom,
% 0.23/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.45     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ C @ A @ D ) ))).
% 0.23/0.45  thf('2', plain,
% 0.23/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.45         ((k2_enumset1 @ X2 @ X0 @ X1 @ X3) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.23/0.45      inference('cnf', [status(esa)], [l123_enumset1])).
% 0.23/0.45  thf('3', plain,
% 0.23/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.45         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.23/0.45      inference('sup+', [status(thm)], ['1', '2'])).
% 0.23/0.45  thf('4', plain,
% 0.23/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.45         ((k2_enumset1 @ X2 @ X0 @ X1 @ X3) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.23/0.45      inference('cnf', [status(esa)], [l123_enumset1])).
% 0.23/0.45  thf('5', plain,
% 0.23/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.45         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.23/0.45      inference('sup+', [status(thm)], ['1', '2'])).
% 0.23/0.45  thf('6', plain,
% 0.23/0.45      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.23/0.45         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.23/0.45      inference('demod', [status(thm)], ['0', '3', '4', '5'])).
% 0.23/0.45  thf('7', plain, ($false), inference('simplify', [status(thm)], ['6'])).
% 0.23/0.45  
% 0.23/0.45  % SZS output end Refutation
% 0.23/0.45  
% 0.23/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
