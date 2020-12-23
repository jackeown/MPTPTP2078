%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wqZsj2GoUs

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:21 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   29 (  33 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :  232 ( 278 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X9 @ X7 @ X8 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('2',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_D @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X13 @ X12 @ X11 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X9 @ X7 @ X8 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X13 @ X12 @ X11 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X9 @ X7 @ X8 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','7','10','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wqZsj2GoUs
% 0.15/0.38  % Computer   : n004.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 17:25:24 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 22 iterations in 0.039s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.35/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(t123_enumset1, conjecture,
% 0.35/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.53     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ B @ C @ A ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.53        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ B @ C @ A ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t123_enumset1])).
% 0.35/0.53  thf('0', plain,
% 0.35/0.53      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.35/0.53         != (k2_enumset1 @ sk_D @ sk_B @ sk_C @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(t105_enumset1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.53     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.35/0.53         ((k2_enumset1 @ X6 @ X9 @ X7 @ X8) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.35/0.53      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.35/0.53         != (k2_enumset1 @ sk_D @ sk_A @ sk_B @ sk_C))),
% 0.35/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.35/0.53  thf(commutativity_k2_tarski, axiom,
% 0.35/0.53    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.35/0.53  thf('3', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.35/0.53      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.35/0.53  thf(l53_enumset1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.53     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.35/0.53       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.53         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 0.35/0.53           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 0.35/0.53      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.35/0.53  thf('5', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.53         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2)
% 0.35/0.53           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.53         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 0.35/0.53           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 0.35/0.53      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.53         ((k2_enumset1 @ X2 @ X3 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['5', '6'])).
% 0.35/0.53  thf(t107_enumset1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.53     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 0.35/0.53  thf('8', plain,
% 0.35/0.53      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.35/0.53         ((k2_enumset1 @ X10 @ X13 @ X12 @ X11)
% 0.35/0.53           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.35/0.53      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.35/0.53  thf('9', plain,
% 0.35/0.53      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.35/0.53         ((k2_enumset1 @ X6 @ X9 @ X7 @ X8) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.35/0.53      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.35/0.53  thf('10', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.53         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X1 @ X2 @ X0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['8', '9'])).
% 0.35/0.53  thf('11', plain,
% 0.35/0.53      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.35/0.53         ((k2_enumset1 @ X10 @ X13 @ X12 @ X11)
% 0.35/0.53           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.35/0.53      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.35/0.53  thf('12', plain,
% 0.35/0.53      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.35/0.53         ((k2_enumset1 @ X6 @ X9 @ X7 @ X8) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.35/0.53      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.53         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['11', '12'])).
% 0.35/0.53  thf('14', plain,
% 0.35/0.53      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.35/0.53         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.35/0.53      inference('demod', [status(thm)], ['2', '7', '10', '13'])).
% 0.35/0.53  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
