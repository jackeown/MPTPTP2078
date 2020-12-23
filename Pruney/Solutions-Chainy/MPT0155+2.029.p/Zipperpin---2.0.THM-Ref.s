%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eEU5pTSExg

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:30 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  297 ( 399 expanded)
%              Number of equality atoms :   26 (  35 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t71_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_enumset1 @ A @ A @ B @ C )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k2_tarski @ X19 @ X20 ) @ ( k1_enumset1 @ X21 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('17',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','15','16'])).

thf('18',plain,(
    $false ),
    inference(simplify,[status(thm)],['17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eEU5pTSExg
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:13:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 62 iterations in 0.043s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.19/0.46  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.19/0.46  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(t71_enumset1, conjecture,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.46        ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t71_enumset1])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (((k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.19/0.46         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t69_enumset1, axiom,
% 0.19/0.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.46  thf('1', plain, (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 0.19/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.46  thf(t48_enumset1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.46     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.19/0.46       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.46         ((k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.19/0.46           = (k2_xboole_0 @ (k2_tarski @ X19 @ X20) @ 
% 0.19/0.46              (k1_enumset1 @ X21 @ X22 @ X23)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.46         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.19/0.46           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.19/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf(t44_enumset1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.19/0.46       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.46         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 0.19/0.46           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.46         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.19/0.46           = (k2_enumset1 @ X0 @ X3 @ X2 @ X1))),
% 0.19/0.46      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.46  thf(t70_enumset1, axiom,
% 0.19/0.46    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X38 : $i, X39 : $i]:
% 0.19/0.46         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.19/0.46      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.46         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 0.19/0.46           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.19/0.46           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.19/0.46      inference('sup+', [status(thm)], ['6', '7'])).
% 0.19/0.46  thf(t42_enumset1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.19/0.46       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.46         ((k1_enumset1 @ X7 @ X8 @ X9)
% 0.19/0.46           = (k2_xboole_0 @ (k1_tarski @ X7) @ (k2_tarski @ X8 @ X9)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.19/0.46  thf('10', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.19/0.46      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.46  thf(t47_enumset1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.46     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.19/0.46       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.46         ((k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.19/0.46           = (k2_xboole_0 @ (k1_tarski @ X14) @ 
% 0.19/0.46              (k2_enumset1 @ X15 @ X16 @ X17 @ X18)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.46         ((k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.19/0.46           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.19/0.46      inference('sup+', [status(thm)], ['10', '11'])).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.46         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 0.19/0.46           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.46         ((k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.19/0.46           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.19/0.46      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 0.19/0.46      inference('sup+', [status(thm)], ['5', '14'])).
% 0.19/0.46  thf('16', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.19/0.46      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.19/0.46         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.46      inference('demod', [status(thm)], ['0', '15', '16'])).
% 0.19/0.46  thf('18', plain, ($false), inference('simplify', [status(thm)], ['17'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
