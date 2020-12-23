%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4VWbGGCYsj

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:21 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   27 (  40 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :  232 ( 375 expanded)
%              Number of equality atoms :   21 (  34 expanded)
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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t118_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ D @ A @ B ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X8 @ X9 )
      = ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t118_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('9',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5','6','7','8'])).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X8 @ X9 )
      = ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t118_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X3 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('15',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','12','13','14'])).

thf('16',plain,(
    $false ),
    inference(simplify,[status(thm)],['15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4VWbGGCYsj
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:21:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 20 iterations in 0.074s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.35/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.54  thf(t119_enumset1, conjecture,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ D @ B @ A ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ D @ B @ A ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t119_enumset1])).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.35/0.54         != (k2_enumset1 @ sk_C @ sk_D @ sk_B @ sk_A))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(t105_enumset1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.54         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.35/0.54         != (k2_enumset1 @ sk_C @ sk_A @ sk_D @ sk_B))),
% 0.35/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.35/0.54  thf(t107_enumset1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.35/0.54         ((k2_enumset1 @ X4 @ X7 @ X6 @ X5) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.35/0.54      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.54         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.54         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.35/0.54      inference('sup+', [status(thm)], ['3', '4'])).
% 0.35/0.54  thf(t118_enumset1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ D @ A @ B ) ))).
% 0.35/0.54  thf('6', plain,
% 0.35/0.54      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.54         ((k2_enumset1 @ X10 @ X11 @ X8 @ X9)
% 0.35/0.54           = (k2_enumset1 @ X8 @ X9 @ X10 @ X11))),
% 0.35/0.54      inference('cnf', [status(esa)], [t118_enumset1])).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.54         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.54         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.35/0.54      inference('sup+', [status(thm)], ['3', '4'])).
% 0.35/0.54  thf('9', plain,
% 0.35/0.54      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.35/0.54         != (k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D))),
% 0.35/0.54      inference('demod', [status(thm)], ['2', '5', '6', '7', '8'])).
% 0.35/0.54  thf('10', plain,
% 0.35/0.54      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.54         ((k2_enumset1 @ X10 @ X11 @ X8 @ X9)
% 0.35/0.54           = (k2_enumset1 @ X8 @ X9 @ X10 @ X11))),
% 0.35/0.54      inference('cnf', [status(esa)], [t118_enumset1])).
% 0.35/0.54  thf('11', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.54         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.54         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X3 @ X2 @ X0))),
% 0.35/0.54      inference('sup+', [status(thm)], ['10', '11'])).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.54         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.54         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.35/0.54      inference('sup+', [status(thm)], ['3', '4'])).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.35/0.54         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.35/0.54      inference('demod', [status(thm)], ['9', '12', '13', '14'])).
% 0.35/0.54  thf('16', plain, ($false), inference('simplify', [status(thm)], ['15'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.39/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
