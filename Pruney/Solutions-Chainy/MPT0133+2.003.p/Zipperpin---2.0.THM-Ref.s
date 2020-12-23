%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XxyffqYuPc

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:59 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   38 (  45 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  337 ( 408 expanded)
%              Number of equality atoms :   26 (  33 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t49_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_enumset1 @ A @ B @ C @ D @ E )
        = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_enumset1])).

thf('0',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k2_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

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
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_enumset1 @ sk_C @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['0','11'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XxyffqYuPc
% 0.16/0.37  % Computer   : n017.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 11:17:46 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 23 iterations in 0.021s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.49  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.23/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.49  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.23/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.23/0.49  thf(t49_enumset1, conjecture,
% 0.23/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.23/0.49     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.23/0.49       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.23/0.49        ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.23/0.49          ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t49_enumset1])).
% 0.23/0.49  thf('0', plain,
% 0.23/0.49      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.23/0.49         != (k2_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_C) @ 
% 0.23/0.49             (k2_tarski @ sk_D @ sk_E)))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(t42_enumset1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.23/0.49       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.23/0.49  thf('1', plain,
% 0.23/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.49         ((k1_enumset1 @ X5 @ X6 @ X7)
% 0.23/0.49           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k2_tarski @ X6 @ X7)))),
% 0.23/0.49      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.23/0.49  thf(t41_enumset1, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( k2_tarski @ A @ B ) =
% 0.23/0.49       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.23/0.49  thf('2', plain,
% 0.23/0.49      (![X3 : $i, X4 : $i]:
% 0.23/0.49         ((k2_tarski @ X3 @ X4)
% 0.23/0.49           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_tarski @ X4)))),
% 0.23/0.49      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.23/0.49  thf('3', plain,
% 0.23/0.49      (![X3 : $i, X4 : $i]:
% 0.23/0.49         ((k2_tarski @ X3 @ X4)
% 0.23/0.49           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_tarski @ X4)))),
% 0.23/0.49      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.23/0.49  thf(t4_xboole_1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.23/0.49       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.23/0.49  thf('4', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.49         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.23/0.49           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.23/0.49      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.23/0.49  thf('5', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.49         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.23/0.49           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.23/0.49              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.23/0.49      inference('sup+', [status(thm)], ['3', '4'])).
% 0.23/0.49  thf('6', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.49         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.23/0.49           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.23/0.49      inference('sup+', [status(thm)], ['2', '5'])).
% 0.23/0.49  thf('7', plain,
% 0.23/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.49         ((k1_enumset1 @ X5 @ X6 @ X7)
% 0.23/0.49           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k2_tarski @ X6 @ X7)))),
% 0.23/0.49      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.23/0.49  thf('8', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.49         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.23/0.49           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.23/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.23/0.49  thf('9', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.49         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.23/0.49           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.23/0.49      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.23/0.49  thf('10', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.49         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.23/0.49           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.23/0.49              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.23/0.49      inference('sup+', [status(thm)], ['8', '9'])).
% 0.23/0.49  thf('11', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.23/0.49         ((k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.23/0.49           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.23/0.49              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.23/0.49      inference('sup+', [status(thm)], ['1', '10'])).
% 0.23/0.49  thf('12', plain,
% 0.23/0.49      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.23/0.49         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49             (k1_enumset1 @ sk_C @ sk_D @ sk_E)))),
% 0.23/0.49      inference('demod', [status(thm)], ['0', '11'])).
% 0.23/0.49  thf(t44_enumset1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.49     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.23/0.49       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.23/0.49  thf('13', plain,
% 0.23/0.49      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.23/0.49         ((k2_enumset1 @ X8 @ X9 @ X10 @ X11)
% 0.23/0.49           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k1_enumset1 @ X9 @ X10 @ X11)))),
% 0.23/0.49      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.23/0.49  thf('14', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.49         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.23/0.49           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.23/0.49              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.23/0.49      inference('sup+', [status(thm)], ['3', '4'])).
% 0.23/0.49  thf('15', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.23/0.49         ((k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.23/0.49           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.23/0.49              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.23/0.49      inference('sup+', [status(thm)], ['13', '14'])).
% 0.23/0.49  thf(t47_enumset1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.23/0.49     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.23/0.49       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.23/0.49  thf('16', plain,
% 0.23/0.49      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.49         ((k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.23/0.49           = (k2_xboole_0 @ (k1_tarski @ X12) @ 
% 0.23/0.49              (k2_enumset1 @ X13 @ X14 @ X15 @ X16)))),
% 0.23/0.49      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.23/0.49  thf('17', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.23/0.49         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.23/0.49           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.23/0.49              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.23/0.49      inference('sup+', [status(thm)], ['15', '16'])).
% 0.23/0.49  thf('18', plain,
% 0.23/0.49      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.23/0.49         != (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.23/0.49      inference('demod', [status(thm)], ['12', '17'])).
% 0.23/0.49  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.23/0.49  
% 0.23/0.49  % SZS output end Refutation
% 0.23/0.49  
% 0.23/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
