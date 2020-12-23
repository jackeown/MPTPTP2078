%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SvGVi57Zg0

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:39 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   39 (  48 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :  327 ( 423 expanded)
%              Number of equality atoms :   30 (  39 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(t137_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t137_enumset1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k3_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_enumset1 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X9 @ X12 @ X10 @ X11 )
      = ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X19 @ X19 @ X20 @ X21 )
      = ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t112_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ A @ C ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X15 @ X13 @ X16 @ X14 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t112_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X9 @ X12 @ X10 @ X11 )
      = ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X9 @ X12 @ X10 @ X11 )
      = ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('13',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X19 @ X19 @ X20 @ X21 )
      = ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X15 @ X13 @ X16 @ X14 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t112_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X2 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X15 @ X13 @ X16 @ X14 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t112_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X2 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','3','4','11','20'])).

thf('22',plain,(
    $false ),
    inference(simplify,[status(thm)],['21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SvGVi57Zg0
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:48:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.44/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.66  % Solved by: fo/fo7.sh
% 0.44/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.66  % done 334 iterations in 0.212s
% 0.44/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.66  % SZS output start Refutation
% 0.44/0.66  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.44/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.66  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.44/0.66  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.44/0.66  thf(t137_enumset1, conjecture,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.44/0.66       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.44/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.66        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.44/0.66          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.44/0.66    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 0.44/0.66  thf('0', plain,
% 0.44/0.66      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.44/0.66         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(t70_enumset1, axiom,
% 0.44/0.66    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.44/0.66  thf('1', plain,
% 0.44/0.66      (![X17 : $i, X18 : $i]:
% 0.44/0.66         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.44/0.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.44/0.66  thf(l57_enumset1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.44/0.66     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.44/0.66       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.44/0.66  thf('2', plain,
% 0.44/0.66      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.66         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 0.44/0.66           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 0.44/0.66              (k2_tarski @ X7 @ X8)))),
% 0.44/0.66      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.44/0.66  thf('3', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.66         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 0.44/0.66           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.44/0.66      inference('sup+', [status(thm)], ['1', '2'])).
% 0.44/0.66  thf(t72_enumset1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.66     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.44/0.66  thf('4', plain,
% 0.44/0.66      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.44/0.66         ((k3_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25)
% 0.44/0.66           = (k2_enumset1 @ X22 @ X23 @ X24 @ X25))),
% 0.44/0.66      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.44/0.66  thf(t105_enumset1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.66     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 0.44/0.66  thf('5', plain,
% 0.44/0.66      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.66         ((k2_enumset1 @ X9 @ X12 @ X10 @ X11)
% 0.44/0.66           = (k2_enumset1 @ X9 @ X10 @ X11 @ X12))),
% 0.44/0.66      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.44/0.66  thf(t71_enumset1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.44/0.66  thf('6', plain,
% 0.44/0.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.44/0.66         ((k2_enumset1 @ X19 @ X19 @ X20 @ X21)
% 0.44/0.66           = (k1_enumset1 @ X19 @ X20 @ X21))),
% 0.44/0.66      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.44/0.66  thf('7', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 0.44/0.66      inference('sup+', [status(thm)], ['5', '6'])).
% 0.44/0.66  thf(t112_enumset1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.66     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ A @ C ) ))).
% 0.44/0.66  thf('8', plain,
% 0.44/0.66      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.66         ((k2_enumset1 @ X15 @ X13 @ X16 @ X14)
% 0.44/0.66           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 0.44/0.66      inference('cnf', [status(esa)], [t112_enumset1])).
% 0.44/0.66  thf('9', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X1 @ X2 @ X2))),
% 0.44/0.66      inference('sup+', [status(thm)], ['7', '8'])).
% 0.44/0.66  thf('10', plain,
% 0.44/0.66      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.66         ((k2_enumset1 @ X9 @ X12 @ X10 @ X11)
% 0.44/0.66           = (k2_enumset1 @ X9 @ X10 @ X11 @ X12))),
% 0.44/0.66      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.44/0.66  thf('11', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         ((k2_enumset1 @ X0 @ X2 @ X1 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['9', '10'])).
% 0.44/0.66  thf('12', plain,
% 0.44/0.66      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.66         ((k2_enumset1 @ X9 @ X12 @ X10 @ X11)
% 0.44/0.66           = (k2_enumset1 @ X9 @ X10 @ X11 @ X12))),
% 0.44/0.66      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.44/0.66  thf('13', plain,
% 0.44/0.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.44/0.66         ((k2_enumset1 @ X19 @ X19 @ X20 @ X21)
% 0.44/0.66           = (k1_enumset1 @ X19 @ X20 @ X21))),
% 0.44/0.66      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.44/0.66  thf('14', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.44/0.66      inference('sup+', [status(thm)], ['12', '13'])).
% 0.44/0.66  thf('15', plain,
% 0.44/0.66      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.66         ((k2_enumset1 @ X15 @ X13 @ X16 @ X14)
% 0.44/0.66           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 0.44/0.66      inference('cnf', [status(esa)], [t112_enumset1])).
% 0.44/0.66  thf('16', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X2 @ X2 @ X0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['14', '15'])).
% 0.44/0.66  thf('17', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.44/0.66      inference('sup+', [status(thm)], ['12', '13'])).
% 0.44/0.66  thf('18', plain,
% 0.44/0.66      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.66         ((k2_enumset1 @ X15 @ X13 @ X16 @ X14)
% 0.44/0.66           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 0.44/0.66      inference('cnf', [status(esa)], [t112_enumset1])).
% 0.44/0.66  thf('19', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         ((k2_enumset1 @ X0 @ X2 @ X2 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['17', '18'])).
% 0.44/0.66  thf('20', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.44/0.66      inference('sup+', [status(thm)], ['16', '19'])).
% 0.44/0.66  thf('21', plain,
% 0.44/0.66      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.44/0.66         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.44/0.66      inference('demod', [status(thm)], ['0', '3', '4', '11', '20'])).
% 0.44/0.66  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 0.44/0.66  
% 0.44/0.66  % SZS output end Refutation
% 0.44/0.66  
% 0.44/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
