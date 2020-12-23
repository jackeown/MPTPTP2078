%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RndqRqIoCC

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:22 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   23 (  27 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :  188 ( 232 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :   11 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t123_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ B @ C @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ D @ B @ C @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t123_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_D @ sk_B @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l123_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ C @ A @ D ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X3 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l123_enumset1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X3 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l123_enumset1])).

thf('3',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_B @ sk_C @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X7 @ X5 @ X6 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X3 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l123_enumset1])).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X7 @ X5 @ X6 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('7',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X8 @ X11 @ X10 @ X9 )
      = ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X7 @ X5 @ X6 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    $false ),
    inference(simplify,[status(thm)],['11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RndqRqIoCC
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.70  % Solved by: fo/fo7.sh
% 0.44/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.70  % done 25 iterations in 0.209s
% 0.44/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.70  % SZS output start Refutation
% 0.44/0.70  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.44/0.70  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.70  thf(t123_enumset1, conjecture,
% 0.44/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.70     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ B @ C @ A ) ))).
% 0.44/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.70    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.70        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ B @ C @ A ) ) )),
% 0.44/0.70    inference('cnf.neg', [status(esa)], [t123_enumset1])).
% 0.44/0.70  thf('0', plain,
% 0.44/0.70      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.44/0.70         != (k2_enumset1 @ sk_D @ sk_B @ sk_C @ sk_A))),
% 0.44/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.70  thf(l123_enumset1, axiom,
% 0.44/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.70     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ C @ A @ D ) ))).
% 0.44/0.70  thf('1', plain,
% 0.44/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.70         ((k2_enumset1 @ X2 @ X0 @ X1 @ X3) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.44/0.70      inference('cnf', [status(esa)], [l123_enumset1])).
% 0.44/0.70  thf('2', plain,
% 0.44/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.70         ((k2_enumset1 @ X2 @ X0 @ X1 @ X3) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.44/0.70      inference('cnf', [status(esa)], [l123_enumset1])).
% 0.44/0.70  thf('3', plain,
% 0.44/0.70      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.44/0.70         != (k2_enumset1 @ sk_B @ sk_C @ sk_D @ sk_A))),
% 0.44/0.70      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.44/0.70  thf(t105_enumset1, axiom,
% 0.44/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.70     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 0.44/0.70  thf('4', plain,
% 0.44/0.70      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.44/0.70         ((k2_enumset1 @ X4 @ X7 @ X5 @ X6) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.44/0.70      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.44/0.70  thf('5', plain,
% 0.44/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.70         ((k2_enumset1 @ X2 @ X0 @ X1 @ X3) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.44/0.70      inference('cnf', [status(esa)], [l123_enumset1])).
% 0.44/0.70  thf('6', plain,
% 0.44/0.70      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.44/0.70         ((k2_enumset1 @ X4 @ X7 @ X5 @ X6) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.44/0.70      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.44/0.70  thf('7', plain,
% 0.44/0.70      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.44/0.70         != (k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C))),
% 0.44/0.70      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.44/0.70  thf(t107_enumset1, axiom,
% 0.44/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.70     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 0.44/0.70  thf('8', plain,
% 0.44/0.70      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.44/0.70         ((k2_enumset1 @ X8 @ X11 @ X10 @ X9)
% 0.44/0.70           = (k2_enumset1 @ X8 @ X9 @ X10 @ X11))),
% 0.44/0.70      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.44/0.70  thf('9', plain,
% 0.44/0.70      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.44/0.70         ((k2_enumset1 @ X4 @ X7 @ X5 @ X6) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.44/0.70      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.44/0.70  thf('10', plain,
% 0.44/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.70         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.44/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.44/0.70  thf('11', plain,
% 0.44/0.70      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.44/0.70         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.44/0.70      inference('demod', [status(thm)], ['7', '10'])).
% 0.44/0.70  thf('12', plain, ($false), inference('simplify', [status(thm)], ['11'])).
% 0.44/0.70  
% 0.44/0.70  % SZS output end Refutation
% 0.44/0.70  
% 0.44/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
