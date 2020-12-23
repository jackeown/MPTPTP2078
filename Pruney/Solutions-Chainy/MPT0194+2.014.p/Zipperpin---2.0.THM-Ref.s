%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nZCfENGghd

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:16 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   19 (  21 expanded)
%              Number of leaves         :    8 (  10 expanded)
%              Depth                    :    5
%              Number of atoms          :  144 ( 166 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t112_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ A @ C ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X6 @ X4 @ X7 @ X5 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t112_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t111_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X6 @ X4 @ X7 @ X5 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t112_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nZCfENGghd
% 0.13/0.38  % Computer   : n023.cluster.edu
% 0.13/0.38  % Model      : x86_64 x86_64
% 0.13/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.38  % Memory     : 8042.1875MB
% 0.13/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.38  % CPULimit   : 60
% 0.13/0.38  % DateTime   : Tue Dec  1 11:34:21 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.58/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.79  % Solved by: fo/fo7.sh
% 0.58/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.79  % done 74 iterations in 0.323s
% 0.58/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.79  % SZS output start Refutation
% 0.58/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.79  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.58/0.79  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.79  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.79  thf(t113_enumset1, conjecture,
% 0.58/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.79     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ C @ A ) ))).
% 0.58/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.79    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.79        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ C @ A ) ) )),
% 0.58/0.79    inference('cnf.neg', [status(esa)], [t113_enumset1])).
% 0.58/0.79  thf('0', plain,
% 0.58/0.79      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.58/0.79         != (k2_enumset1 @ sk_B @ sk_D @ sk_C @ sk_A))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(t111_enumset1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.79     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ C @ D @ A ) ))).
% 0.58/0.79  thf('1', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.79         ((k2_enumset1 @ X3 @ X0 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.58/0.79      inference('cnf', [status(esa)], [t111_enumset1])).
% 0.58/0.79  thf('2', plain,
% 0.58/0.79      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.58/0.79         != (k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C))),
% 0.58/0.79      inference('demod', [status(thm)], ['0', '1'])).
% 0.58/0.79  thf(t112_enumset1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.79     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ A @ C ) ))).
% 0.58/0.79  thf('3', plain,
% 0.58/0.79      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.58/0.79         ((k2_enumset1 @ X6 @ X4 @ X7 @ X5) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.58/0.79      inference('cnf', [status(esa)], [t112_enumset1])).
% 0.58/0.79  thf('4', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.79         ((k2_enumset1 @ X3 @ X0 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.58/0.79      inference('cnf', [status(esa)], [t111_enumset1])).
% 0.58/0.79  thf('5', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.79         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X3 @ X1 @ X2))),
% 0.58/0.79      inference('sup+', [status(thm)], ['3', '4'])).
% 0.58/0.79  thf('6', plain,
% 0.58/0.79      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.58/0.79         ((k2_enumset1 @ X6 @ X4 @ X7 @ X5) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.58/0.79      inference('cnf', [status(esa)], [t112_enumset1])).
% 0.58/0.79  thf('7', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.79         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X0 @ X1))),
% 0.58/0.79      inference('sup+', [status(thm)], ['5', '6'])).
% 0.58/0.79  thf('8', plain,
% 0.58/0.79      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.58/0.79         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.58/0.79      inference('demod', [status(thm)], ['2', '7'])).
% 0.58/0.79  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.58/0.79  
% 0.58/0.79  % SZS output end Refutation
% 0.58/0.79  
% 0.58/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
