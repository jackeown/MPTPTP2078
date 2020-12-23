%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RhtANm0JTq

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:37 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :  214 ( 214 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

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
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k3_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X8 @ X9 @ X10 ) @ ( k2_tarski @ X11 @ X12 ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(l129_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ B @ A @ D ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X6 @ X5 @ X4 @ X7 )
      = ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l129_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X23 @ X23 @ X24 @ X25 )
      = ( k1_enumset1 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X16 @ X14 @ X15 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X2 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','3','4','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RhtANm0JTq
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:46:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 258 iterations in 0.151s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.61  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.37/0.61  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.37/0.61  thf(t137_enumset1, conjecture,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.37/0.61       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.61        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.37/0.61          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 0.37/0.61  thf('0', plain,
% 0.37/0.61      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.37/0.61         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(t70_enumset1, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      (![X21 : $i, X22 : $i]:
% 0.37/0.61         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.37/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.61  thf(l57_enumset1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.37/0.61     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.37/0.61       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.61         ((k3_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.37/0.61           = (k2_xboole_0 @ (k1_enumset1 @ X8 @ X9 @ X10) @ 
% 0.37/0.61              (k2_tarski @ X11 @ X12)))),
% 0.37/0.61      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.37/0.61  thf('3', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.61         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 0.37/0.61           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.37/0.61      inference('sup+', [status(thm)], ['1', '2'])).
% 0.37/0.61  thf(t72_enumset1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.61     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.37/0.61  thf('4', plain,
% 0.37/0.61      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.37/0.61         ((k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29)
% 0.37/0.61           = (k2_enumset1 @ X26 @ X27 @ X28 @ X29))),
% 0.37/0.61      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.37/0.61  thf(l129_enumset1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.61     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ B @ A @ D ) ))).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.61         ((k2_enumset1 @ X6 @ X5 @ X4 @ X7) = (k2_enumset1 @ X4 @ X5 @ X6 @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [l129_enumset1])).
% 0.37/0.61  thf(t71_enumset1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.37/0.61  thf('6', plain,
% 0.37/0.61      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.37/0.61         ((k2_enumset1 @ X23 @ X23 @ X24 @ X25)
% 0.37/0.61           = (k1_enumset1 @ X23 @ X24 @ X25))),
% 0.37/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.37/0.61  thf('7', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.61  thf(t105_enumset1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.61     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 0.37/0.61  thf('8', plain,
% 0.37/0.61      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.61         ((k2_enumset1 @ X13 @ X16 @ X14 @ X15)
% 0.37/0.61           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 0.37/0.61      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.37/0.61  thf('9', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X2 @ X0 @ X2))),
% 0.37/0.61      inference('sup+', [status(thm)], ['7', '8'])).
% 0.37/0.61  thf('10', plain,
% 0.37/0.61      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.37/0.61         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['0', '3', '4', '9'])).
% 0.37/0.61  thf('11', plain, ($false), inference('simplify', [status(thm)], ['10'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
