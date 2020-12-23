%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iJ9vueuTk7

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :  226 ( 226 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t55_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
        = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) ),
    inference('cnf.neg',[status(esa)],[t55_enumset1])).

thf('0',plain,(
    ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k2_xboole_0 @ ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_tarski @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

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
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t54_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 ) @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iJ9vueuTk7
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:13:22 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 31 iterations in 0.029s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.22/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.22/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.49  thf(t55_enumset1, conjecture,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.49     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.22/0.49       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.49        ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.22/0.49          ( k2_xboole_0 @
% 0.22/0.49            ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t55_enumset1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (((k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.22/0.49         != (k2_xboole_0 @ (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.22/0.49             (k1_tarski @ sk_F)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t41_enumset1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k2_tarski @ A @ B ) =
% 0.22/0.49       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i]:
% 0.22/0.49         ((k2_tarski @ X3 @ X4)
% 0.22/0.49           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_tarski @ X4)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.22/0.49  thf(t50_enumset1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.49     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.22/0.49       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.49         ((k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.22/0.49           = (k2_xboole_0 @ (k2_enumset1 @ X12 @ X13 @ X14 @ X15) @ 
% 0.22/0.49              (k1_tarski @ X16)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.22/0.49  thf(t4_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.49       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.22/0.49           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 0.22/0.49           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 0.22/0.49              (k2_xboole_0 @ (k1_tarski @ X0) @ X5)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         ((k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.22/0.49           (k1_tarski @ X0))
% 0.22/0.49           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.22/0.49              (k2_tarski @ X1 @ X0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['1', '4'])).
% 0.22/0.49  thf(t54_enumset1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.49     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.22/0.49       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ))).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.49         ((k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22)
% 0.22/0.49           = (k2_xboole_0 @ (k2_enumset1 @ X17 @ X18 @ X19 @ X20) @ 
% 0.22/0.49              (k2_tarski @ X21 @ X22)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t54_enumset1])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         ((k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.22/0.49           (k1_tarski @ X0)) = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (((k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.22/0.50         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '7'])).
% 0.22/0.50  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
