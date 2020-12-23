%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4DGIJuRKsE

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:18 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   29 (  39 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  254 ( 364 expanded)
%              Number of equality atoms :   23 (  33 expanded)
%              Maximal formula depth    :   11 (   8 average)

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

thf(t117_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ B @ D @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ C @ B @ D @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t117_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_C @ sk_B @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t108_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ A @ C @ D ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X2 @ X3 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t108_enumset1])).

thf('2',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_B @ sk_C @ sk_D @ sk_A ) ),
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
      ( ( k2_enumset1 @ X1 @ X0 @ X2 @ X3 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t108_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X3 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X6 @ X4 @ X7 @ X5 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t112_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X2 @ X3 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t108_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X0 @ X2 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X3 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X6 @ X4 @ X7 @ X5 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t112_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X6 @ X4 @ X7 @ X5 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t112_enumset1])).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X6 @ X4 @ X7 @ X5 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t112_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4DGIJuRKsE
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:32:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.52/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.73  % Solved by: fo/fo7.sh
% 0.52/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.73  % done 143 iterations in 0.272s
% 0.52/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.73  % SZS output start Refutation
% 0.52/0.73  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.52/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.73  thf(sk_D_type, type, sk_D: $i).
% 0.52/0.73  thf(t117_enumset1, conjecture,
% 0.52/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ B @ D @ A ) ))).
% 0.52/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.73    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ B @ D @ A ) ) )),
% 0.52/0.73    inference('cnf.neg', [status(esa)], [t117_enumset1])).
% 0.52/0.73  thf('0', plain,
% 0.52/0.73      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.52/0.73         != (k2_enumset1 @ sk_C @ sk_B @ sk_D @ sk_A))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(t108_enumset1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 0.52/0.73  thf('1', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.73         ((k2_enumset1 @ X1 @ X0 @ X2 @ X3) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.52/0.73      inference('cnf', [status(esa)], [t108_enumset1])).
% 0.52/0.73  thf('2', plain,
% 0.52/0.73      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.52/0.73         != (k2_enumset1 @ sk_B @ sk_C @ sk_D @ sk_A))),
% 0.52/0.73      inference('demod', [status(thm)], ['0', '1'])).
% 0.52/0.73  thf(t112_enumset1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ A @ C ) ))).
% 0.52/0.73  thf('3', plain,
% 0.52/0.73      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.52/0.73         ((k2_enumset1 @ X6 @ X4 @ X7 @ X5) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.52/0.73      inference('cnf', [status(esa)], [t112_enumset1])).
% 0.52/0.73  thf('4', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.73         ((k2_enumset1 @ X1 @ X0 @ X2 @ X3) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.52/0.73      inference('cnf', [status(esa)], [t108_enumset1])).
% 0.52/0.73  thf('5', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.73         ((k2_enumset1 @ X0 @ X2 @ X3 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['3', '4'])).
% 0.52/0.73  thf('6', plain,
% 0.52/0.73      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.52/0.73         != (k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D))),
% 0.52/0.73      inference('demod', [status(thm)], ['2', '5'])).
% 0.52/0.73  thf('7', plain,
% 0.52/0.73      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.52/0.73         ((k2_enumset1 @ X6 @ X4 @ X7 @ X5) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.52/0.73      inference('cnf', [status(esa)], [t112_enumset1])).
% 0.52/0.73  thf('8', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.73         ((k2_enumset1 @ X1 @ X0 @ X2 @ X3) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.52/0.73      inference('cnf', [status(esa)], [t108_enumset1])).
% 0.52/0.73  thf('9', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.73         ((k2_enumset1 @ X3 @ X1 @ X0 @ X2) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['7', '8'])).
% 0.52/0.73  thf('10', plain,
% 0.52/0.73      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.52/0.73         != (k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C))),
% 0.52/0.73      inference('demod', [status(thm)], ['6', '9'])).
% 0.52/0.73  thf('11', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.73         ((k2_enumset1 @ X0 @ X2 @ X3 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['3', '4'])).
% 0.52/0.73  thf('12', plain,
% 0.52/0.73      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.52/0.73         ((k2_enumset1 @ X6 @ X4 @ X7 @ X5) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.52/0.73      inference('cnf', [status(esa)], [t112_enumset1])).
% 0.52/0.73  thf('13', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.73         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['11', '12'])).
% 0.52/0.73  thf('14', plain,
% 0.52/0.73      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.52/0.73         ((k2_enumset1 @ X6 @ X4 @ X7 @ X5) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.52/0.73      inference('cnf', [status(esa)], [t112_enumset1])).
% 0.52/0.73  thf('15', plain,
% 0.52/0.73      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.52/0.73         ((k2_enumset1 @ X6 @ X4 @ X7 @ X5) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.52/0.73      inference('cnf', [status(esa)], [t112_enumset1])).
% 0.52/0.73  thf('16', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.73         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.52/0.73      inference('sup+', [status(thm)], ['14', '15'])).
% 0.52/0.73  thf('17', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.73         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['13', '16'])).
% 0.52/0.73  thf('18', plain,
% 0.52/0.73      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.52/0.73         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.52/0.73      inference('demod', [status(thm)], ['10', '17'])).
% 0.52/0.73  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.52/0.73  
% 0.52/0.73  % SZS output end Refutation
% 0.52/0.73  
% 0.52/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
