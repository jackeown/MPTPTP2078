%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fTWdYTyeOY

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:21 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   29 (  43 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  254 ( 408 expanded)
%              Number of equality atoms :   23 (  37 expanded)
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

thf(t119_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ D @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ C @ D @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t119_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_C @ sk_D @ sk_B @ sk_A ) ),
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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X2 @ X3 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('7',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['2','5','6'])).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X6 @ X5 @ X4 @ X7 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t116_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X3 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('12',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['7','10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X2 @ X3 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X6 @ X5 @ X4 @ X7 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t116_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X3 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X3 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fTWdYTyeOY
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:47:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.68/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.85  % Solved by: fo/fo7.sh
% 0.68/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.85  % done 200 iterations in 0.389s
% 0.68/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.85  % SZS output start Refutation
% 0.68/0.85  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.68/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.85  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.85  thf(sk_D_type, type, sk_D: $i).
% 0.68/0.85  thf(t119_enumset1, conjecture,
% 0.68/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.85     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ D @ B @ A ) ))).
% 0.68/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.85    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.85        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ D @ B @ A ) ) )),
% 0.68/0.85    inference('cnf.neg', [status(esa)], [t119_enumset1])).
% 0.68/0.85  thf('0', plain,
% 0.68/0.85      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.68/0.85         != (k2_enumset1 @ sk_C @ sk_D @ sk_B @ sk_A))),
% 0.68/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.85  thf(t105_enumset1, axiom,
% 0.68/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.85     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 0.68/0.85  thf('1', plain,
% 0.68/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.85         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.68/0.85      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.68/0.85  thf('2', plain,
% 0.68/0.85      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.68/0.85         != (k2_enumset1 @ sk_C @ sk_A @ sk_D @ sk_B))),
% 0.68/0.85      inference('demod', [status(thm)], ['0', '1'])).
% 0.68/0.85  thf(t116_enumset1, axiom,
% 0.68/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.85     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ B @ A @ D ) ))).
% 0.68/0.85  thf('3', plain,
% 0.68/0.85      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.68/0.85         ((k2_enumset1 @ X6 @ X5 @ X4 @ X7) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.68/0.85      inference('cnf', [status(esa)], [t116_enumset1])).
% 0.68/0.85  thf('4', plain,
% 0.68/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.85         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.68/0.85      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.68/0.85  thf('5', plain,
% 0.68/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.85         ((k2_enumset1 @ X1 @ X0 @ X2 @ X3) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.68/0.85      inference('sup+', [status(thm)], ['3', '4'])).
% 0.68/0.85  thf('6', plain,
% 0.68/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.85         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.68/0.85      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.68/0.85  thf('7', plain,
% 0.68/0.85      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.68/0.85         != (k2_enumset1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.68/0.85      inference('demod', [status(thm)], ['2', '5', '6'])).
% 0.68/0.85  thf('8', plain,
% 0.68/0.85      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.68/0.85         ((k2_enumset1 @ X6 @ X5 @ X4 @ X7) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.68/0.85      inference('cnf', [status(esa)], [t116_enumset1])).
% 0.68/0.85  thf('9', plain,
% 0.68/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.85         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.68/0.85      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.68/0.85  thf('10', plain,
% 0.68/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.85         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X3 @ X0 @ X2))),
% 0.68/0.85      inference('sup+', [status(thm)], ['8', '9'])).
% 0.68/0.85  thf('11', plain,
% 0.68/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.85         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.68/0.85      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.68/0.85  thf('12', plain,
% 0.68/0.85      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.68/0.85         != (k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C))),
% 0.68/0.85      inference('demod', [status(thm)], ['7', '10', '11'])).
% 0.68/0.85  thf('13', plain,
% 0.68/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.85         ((k2_enumset1 @ X1 @ X0 @ X2 @ X3) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.68/0.85      inference('sup+', [status(thm)], ['3', '4'])).
% 0.68/0.85  thf('14', plain,
% 0.68/0.85      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.68/0.85         ((k2_enumset1 @ X6 @ X5 @ X4 @ X7) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.68/0.85      inference('cnf', [status(esa)], [t116_enumset1])).
% 0.68/0.85  thf('15', plain,
% 0.68/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.85         ((k2_enumset1 @ X2 @ X0 @ X1 @ X3) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.68/0.85      inference('sup+', [status(thm)], ['13', '14'])).
% 0.68/0.85  thf('16', plain,
% 0.68/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.85         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X3 @ X0 @ X2))),
% 0.68/0.85      inference('sup+', [status(thm)], ['8', '9'])).
% 0.68/0.85  thf('17', plain,
% 0.68/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.85         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.68/0.85      inference('sup+', [status(thm)], ['15', '16'])).
% 0.68/0.85  thf('18', plain,
% 0.68/0.85      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.68/0.85         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.68/0.85      inference('demod', [status(thm)], ['12', '17'])).
% 0.68/0.85  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.68/0.85  
% 0.68/0.85  % SZS output end Refutation
% 0.68/0.85  
% 0.68/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
