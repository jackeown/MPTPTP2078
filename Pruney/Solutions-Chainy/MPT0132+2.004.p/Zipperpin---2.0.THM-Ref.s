%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fzbjRV5xZa

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:59 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  266 ( 297 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t48_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_enumset1 @ A @ B @ C @ D @ E )
        = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_enumset1])).

thf('0',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_enumset1 @ sk_C @ sk_D @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k2_tarski @ X10 @ X11 ) @ ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k2_tarski @ X10 @ X11 ) @ ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k3_enumset1 @ X3 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X4 @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['0','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fzbjRV5xZa
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:01:18 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.18/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.45  % Solved by: fo/fo7.sh
% 0.18/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.45  % done 12 iterations in 0.016s
% 0.18/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.45  % SZS output start Refutation
% 0.18/0.45  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.18/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.45  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.18/0.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.18/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.18/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.18/0.45  thf(sk_D_type, type, sk_D: $i).
% 0.18/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.45  thf(sk_E_type, type, sk_E: $i).
% 0.18/0.45  thf(t48_enumset1, conjecture,
% 0.18/0.45    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.18/0.45     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.18/0.45       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.18/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.45    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.18/0.45        ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.18/0.45          ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )),
% 0.18/0.45    inference('cnf.neg', [status(esa)], [t48_enumset1])).
% 0.18/0.45  thf('0', plain,
% 0.18/0.45      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.18/0.45         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.18/0.45             (k1_enumset1 @ sk_C @ sk_D @ sk_E)))),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf(t41_enumset1, axiom,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ( k2_tarski @ A @ B ) =
% 0.18/0.45       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.18/0.45  thf('1', plain,
% 0.18/0.45      (![X8 : $i, X9 : $i]:
% 0.18/0.45         ((k2_tarski @ X8 @ X9)
% 0.18/0.45           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k1_tarski @ X9)))),
% 0.18/0.45      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.18/0.45  thf('2', plain,
% 0.18/0.45      (![X8 : $i, X9 : $i]:
% 0.18/0.45         ((k2_tarski @ X8 @ X9)
% 0.18/0.45           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k1_tarski @ X9)))),
% 0.18/0.45      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.18/0.45  thf(t4_xboole_1, axiom,
% 0.18/0.45    (![A:$i,B:$i,C:$i]:
% 0.18/0.45     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.18/0.45       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.18/0.45  thf('3', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.45         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.18/0.45           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.18/0.45      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.18/0.45  thf('4', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.45         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.18/0.45           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.18/0.45              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.18/0.45      inference('sup+', [status(thm)], ['2', '3'])).
% 0.18/0.45  thf('5', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.45         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.18/0.45           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.18/0.45      inference('sup+', [status(thm)], ['1', '4'])).
% 0.18/0.45  thf(t43_enumset1, axiom,
% 0.18/0.45    (![A:$i,B:$i,C:$i]:
% 0.18/0.45     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.18/0.45       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.18/0.45  thf('6', plain,
% 0.18/0.45      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.18/0.45         ((k1_enumset1 @ X10 @ X11 @ X12)
% 0.18/0.45           = (k2_xboole_0 @ (k2_tarski @ X10 @ X11) @ (k1_tarski @ X12)))),
% 0.18/0.45      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.18/0.45  thf('7', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.45         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.18/0.45           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.18/0.45      inference('demod', [status(thm)], ['5', '6'])).
% 0.18/0.45  thf('8', plain,
% 0.18/0.45      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.18/0.45         ((k1_enumset1 @ X10 @ X11 @ X12)
% 0.18/0.45           = (k2_xboole_0 @ (k2_tarski @ X10 @ X11) @ (k1_tarski @ X12)))),
% 0.18/0.45      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.18/0.45  thf('9', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.45         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.18/0.45           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.18/0.45      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.18/0.45  thf('10', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.18/0.45         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.18/0.45           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.18/0.45              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.18/0.45      inference('sup+', [status(thm)], ['8', '9'])).
% 0.18/0.45  thf('11', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.18/0.45         ((k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.18/0.45           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.18/0.45              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.18/0.45      inference('sup+', [status(thm)], ['7', '10'])).
% 0.18/0.45  thf(l57_enumset1, axiom,
% 0.18/0.45    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.18/0.45     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.18/0.45       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.18/0.45  thf('12', plain,
% 0.18/0.45      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.18/0.45         ((k3_enumset1 @ X3 @ X4 @ X5 @ X6 @ X7)
% 0.18/0.45           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X4 @ X5) @ 
% 0.18/0.45              (k2_tarski @ X6 @ X7)))),
% 0.18/0.45      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.18/0.45  thf('13', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.18/0.45         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.18/0.45           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.18/0.45              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.18/0.45      inference('demod', [status(thm)], ['11', '12'])).
% 0.18/0.45  thf('14', plain,
% 0.18/0.45      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.18/0.45         != (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.18/0.45      inference('demod', [status(thm)], ['0', '13'])).
% 0.18/0.45  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.18/0.45  
% 0.18/0.45  % SZS output end Refutation
% 0.18/0.45  
% 0.18/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
