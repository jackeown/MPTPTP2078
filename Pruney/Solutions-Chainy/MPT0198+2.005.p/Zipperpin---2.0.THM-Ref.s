%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.353V9y4SrY

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:20 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   24 (  28 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :  199 ( 243 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :   11 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t103_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ D @ C ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('2',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_C @ sk_D @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X7 @ X6 @ X5 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('4',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_C @ sk_B @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t112_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ A @ C ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X10 @ X8 @ X11 @ X9 )
      = ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t112_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('7',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X7 @ X6 @ X5 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X0 @ X2 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('12',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','10','11'])).

thf('13',plain,(
    $false ),
    inference(simplify,[status(thm)],['12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.353V9y4SrY
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 20:41:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 8 iterations in 0.022s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.23/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(t119_enumset1, conjecture,
% 0.23/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.49     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ D @ B @ A ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.49        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ D @ B @ A ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t119_enumset1])).
% 0.23/0.49  thf('0', plain,
% 0.23/0.49      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.23/0.49         != (k2_enumset1 @ sk_C @ sk_D @ sk_B @ sk_A))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(t103_enumset1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.49     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 0.23/0.49  thf('1', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.49         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.23/0.49      inference('cnf', [status(esa)], [t103_enumset1])).
% 0.23/0.49  thf('2', plain,
% 0.23/0.49      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.23/0.49         != (k2_enumset1 @ sk_C @ sk_D @ sk_A @ sk_B))),
% 0.23/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.23/0.49  thf(t107_enumset1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.49     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 0.23/0.49  thf('3', plain,
% 0.23/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.49         ((k2_enumset1 @ X4 @ X7 @ X6 @ X5) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.23/0.49      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.23/0.49  thf('4', plain,
% 0.23/0.49      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.23/0.49         != (k2_enumset1 @ sk_C @ sk_B @ sk_A @ sk_D))),
% 0.23/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.23/0.49  thf(t112_enumset1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.49     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ A @ C ) ))).
% 0.23/0.49  thf('5', plain,
% 0.23/0.49      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.23/0.49         ((k2_enumset1 @ X10 @ X8 @ X11 @ X9)
% 0.23/0.49           = (k2_enumset1 @ X8 @ X9 @ X10 @ X11))),
% 0.23/0.49      inference('cnf', [status(esa)], [t112_enumset1])).
% 0.23/0.49  thf('6', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.49         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.23/0.49      inference('cnf', [status(esa)], [t103_enumset1])).
% 0.23/0.49  thf('7', plain,
% 0.23/0.49      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.23/0.49         != (k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D))),
% 0.23/0.49      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.23/0.49  thf('8', plain,
% 0.23/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.49         ((k2_enumset1 @ X4 @ X7 @ X6 @ X5) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.23/0.49      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.23/0.49  thf('9', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.49         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.23/0.49      inference('cnf', [status(esa)], [t103_enumset1])).
% 0.23/0.49  thf('10', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.49         ((k2_enumset1 @ X3 @ X0 @ X2 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.23/0.49      inference('sup+', [status(thm)], ['8', '9'])).
% 0.23/0.49  thf('11', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.49         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.23/0.49      inference('cnf', [status(esa)], [t103_enumset1])).
% 0.23/0.49  thf('12', plain,
% 0.23/0.49      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.23/0.49         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.23/0.49      inference('demod', [status(thm)], ['7', '10', '11'])).
% 0.23/0.49  thf('13', plain, ($false), inference('simplify', [status(thm)], ['12'])).
% 0.23/0.49  
% 0.23/0.49  % SZS output end Refutation
% 0.23/0.49  
% 0.23/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
