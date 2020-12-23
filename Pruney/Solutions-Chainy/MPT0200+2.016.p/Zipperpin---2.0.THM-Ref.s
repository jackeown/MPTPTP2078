%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zB00jNDQH5

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:25 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   29 (  35 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  254 ( 320 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   11 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t125_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ D @ C @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t125_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
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
 != ( k2_enumset1 @ sk_D @ sk_A @ sk_B @ sk_C ) ),
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
 != ( k2_enumset1 @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t117_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ B @ D @ A ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X11 @ X9 @ X8 @ X10 )
      = ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t117_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X3 @ X0 @ X2 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X6 @ X5 @ X4 @ X7 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t116_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X11 @ X9 @ X8 @ X10 )
      = ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t117_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X11 @ X9 @ X8 @ X10 )
      = ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t117_enumset1])).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X6 @ X5 @ X4 @ X7 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t116_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['8','13','16'])).

thf('18',plain,(
    $false ),
    inference(simplify,[status(thm)],['17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zB00jNDQH5
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 40 iterations in 0.115s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.38/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.56  thf(t125_enumset1, conjecture,
% 0.38/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.56     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.56        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t125_enumset1])).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.38/0.56         != (k2_enumset1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t107_enumset1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.56     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.56         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.38/0.56         != (k2_enumset1 @ sk_D @ sk_A @ sk_B @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['0', '1'])).
% 0.38/0.56  thf(t116_enumset1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.56     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ B @ A @ D ) ))).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.56         ((k2_enumset1 @ X6 @ X5 @ X4 @ X7) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.38/0.56      inference('cnf', [status(esa)], [t116_enumset1])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.38/0.56         != (k2_enumset1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.38/0.56  thf(t117_enumset1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.56     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ B @ D @ A ) ))).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.56         ((k2_enumset1 @ X11 @ X9 @ X8 @ X10)
% 0.38/0.56           = (k2_enumset1 @ X8 @ X9 @ X10 @ X11))),
% 0.38/0.56      inference('cnf', [status(esa)], [t117_enumset1])).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.56         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.56         ((k2_enumset1 @ X1 @ X3 @ X0 @ X2) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['5', '6'])).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.38/0.56         != (k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D))),
% 0.38/0.56      inference('demod', [status(thm)], ['4', '7'])).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.56         ((k2_enumset1 @ X6 @ X5 @ X4 @ X7) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.38/0.56      inference('cnf', [status(esa)], [t116_enumset1])).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.56         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.56         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['9', '10'])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.56         ((k2_enumset1 @ X11 @ X9 @ X8 @ X10)
% 0.38/0.56           = (k2_enumset1 @ X8 @ X9 @ X10 @ X11))),
% 0.38/0.56      inference('cnf', [status(esa)], [t117_enumset1])).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.56         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X0 @ X2 @ X1))),
% 0.38/0.56      inference('sup+', [status(thm)], ['11', '12'])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.56         ((k2_enumset1 @ X11 @ X9 @ X8 @ X10)
% 0.38/0.56           = (k2_enumset1 @ X8 @ X9 @ X10 @ X11))),
% 0.38/0.56      inference('cnf', [status(esa)], [t117_enumset1])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.56         ((k2_enumset1 @ X6 @ X5 @ X4 @ X7) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.38/0.56      inference('cnf', [status(esa)], [t116_enumset1])).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.56         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['14', '15'])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.38/0.56         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.38/0.56      inference('demod', [status(thm)], ['8', '13', '16'])).
% 0.38/0.56  thf('18', plain, ($false), inference('simplify', [status(thm)], ['17'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
