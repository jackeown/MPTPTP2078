%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nlNbaplmhx

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:00 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   45 (  50 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  454 ( 509 expanded)
%              Number of equality atoms :   31 (  36 expanded)
%              Maximal formula depth    :   15 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t51_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
        = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_enumset1])).

thf('0',plain,(
    ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_enumset1 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_tarski @ X14 @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_tarski @ X14 @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf(t113_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ ( k2_xboole_0 @ B @ C ) @ D ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 ) @ X3 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t113_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X4 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X1 ) @ ( k1_tarski @ X0 ) ) @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X17 @ X18 @ X19 ) @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X21 @ X22 @ X23 @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 ) @ X3 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t113_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X3 @ X1 ) @ ( k1_tarski @ X0 ) ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_tarski @ X14 @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','18'])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k4_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X7 @ X8 ) @ ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['0','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nlNbaplmhx
% 0.17/0.38  % Computer   : n020.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 19:23:37 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.25/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.54  % Solved by: fo/fo7.sh
% 0.25/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.54  % done 21 iterations in 0.051s
% 0.25/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.54  % SZS output start Refutation
% 0.25/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.25/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.25/0.54  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.25/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.25/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.25/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.25/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.25/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.25/0.54  thf(sk_F_type, type, sk_F: $i).
% 0.25/0.54  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.25/0.54  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.25/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.54  thf(t51_enumset1, conjecture,
% 0.25/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.25/0.54     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.25/0.54       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.25/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.54    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.25/0.54        ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.25/0.54          ( k2_xboole_0 @
% 0.25/0.54            ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )),
% 0.25/0.54    inference('cnf.neg', [status(esa)], [t51_enumset1])).
% 0.25/0.54  thf('0', plain,
% 0.25/0.54      (((k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.25/0.54         != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.25/0.54             (k3_enumset1 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.25/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.54  thf(t43_enumset1, axiom,
% 0.25/0.54    (![A:$i,B:$i,C:$i]:
% 0.25/0.54     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.25/0.54       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.25/0.54  thf('1', plain,
% 0.25/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.25/0.54         ((k1_enumset1 @ X14 @ X15 @ X16)
% 0.25/0.54           = (k2_xboole_0 @ (k2_tarski @ X14 @ X15) @ (k1_tarski @ X16)))),
% 0.25/0.54      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.25/0.54  thf(t41_enumset1, axiom,
% 0.25/0.54    (![A:$i,B:$i]:
% 0.25/0.54     ( ( k2_tarski @ A @ B ) =
% 0.25/0.54       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.25/0.54  thf('2', plain,
% 0.25/0.54      (![X12 : $i, X13 : $i]:
% 0.25/0.54         ((k2_tarski @ X12 @ X13)
% 0.25/0.54           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13)))),
% 0.25/0.54      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.25/0.54  thf('3', plain,
% 0.25/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.25/0.54         ((k1_enumset1 @ X14 @ X15 @ X16)
% 0.25/0.54           = (k2_xboole_0 @ (k2_tarski @ X14 @ X15) @ (k1_tarski @ X16)))),
% 0.25/0.54      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.25/0.54  thf(t113_xboole_1, axiom,
% 0.25/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.54     ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) =
% 0.25/0.54       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ ( k2_xboole_0 @ B @ C ) @ D ) ) ))).
% 0.25/0.54  thf('4', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.54         ((k2_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2) @ X3)
% 0.25/0.54           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X3)))),
% 0.25/0.54      inference('cnf', [status(esa)], [t113_xboole_1])).
% 0.25/0.54  thf('5', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.25/0.54         ((k2_xboole_0 @ (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4) @ X3)
% 0.25/0.54           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.25/0.54              (k2_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X4) @ X3)))),
% 0.25/0.54      inference('sup+', [status(thm)], ['3', '4'])).
% 0.25/0.54  thf('6', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.25/0.54         ((k2_xboole_0 @ 
% 0.25/0.54           (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X1) @ (k1_tarski @ X0)) @ X2)
% 0.25/0.54           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.25/0.54              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 0.25/0.54      inference('sup+', [status(thm)], ['2', '5'])).
% 0.25/0.54  thf(t46_enumset1, axiom,
% 0.25/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.54     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.25/0.54       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.25/0.54  thf('7', plain,
% 0.25/0.54      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.25/0.54         ((k2_enumset1 @ X17 @ X18 @ X19 @ X20)
% 0.25/0.54           = (k2_xboole_0 @ (k1_enumset1 @ X17 @ X18 @ X19) @ (k1_tarski @ X20)))),
% 0.25/0.54      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.25/0.54  thf('8', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.25/0.54         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X1 @ X0) @ X2)
% 0.25/0.54           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.25/0.54              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 0.25/0.54      inference('demod', [status(thm)], ['6', '7'])).
% 0.25/0.54  thf('9', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.25/0.54         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.25/0.54           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.25/0.54              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.25/0.54      inference('sup+', [status(thm)], ['1', '8'])).
% 0.25/0.54  thf(t50_enumset1, axiom,
% 0.25/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.25/0.54     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.25/0.54       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.25/0.54  thf('10', plain,
% 0.25/0.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.25/0.54         ((k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25)
% 0.25/0.54           = (k2_xboole_0 @ (k2_enumset1 @ X21 @ X22 @ X23 @ X24) @ 
% 0.25/0.54              (k1_tarski @ X25)))),
% 0.25/0.54      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.25/0.54  thf('11', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.25/0.54         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.25/0.54           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.25/0.54              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.25/0.54      inference('sup+', [status(thm)], ['9', '10'])).
% 0.25/0.54  thf('12', plain,
% 0.25/0.54      (![X12 : $i, X13 : $i]:
% 0.25/0.54         ((k2_tarski @ X12 @ X13)
% 0.25/0.54           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13)))),
% 0.25/0.54      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.25/0.54  thf('13', plain,
% 0.25/0.54      (![X12 : $i, X13 : $i]:
% 0.25/0.54         ((k2_tarski @ X12 @ X13)
% 0.25/0.54           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13)))),
% 0.25/0.54      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.25/0.54  thf('14', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.54         ((k2_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2) @ X3)
% 0.25/0.54           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X3)))),
% 0.25/0.54      inference('cnf', [status(esa)], [t113_xboole_1])).
% 0.25/0.54  thf('15', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.54         ((k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3) @ X2)
% 0.25/0.54           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.25/0.54              (k2_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X3) @ X2)))),
% 0.25/0.54      inference('sup+', [status(thm)], ['13', '14'])).
% 0.25/0.54  thf('16', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.54         ((k2_xboole_0 @ 
% 0.25/0.54           (k2_xboole_0 @ (k2_tarski @ X3 @ X1) @ (k1_tarski @ X0)) @ X2)
% 0.25/0.54           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.25/0.54              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 0.25/0.54      inference('sup+', [status(thm)], ['12', '15'])).
% 0.25/0.54  thf('17', plain,
% 0.25/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.25/0.54         ((k1_enumset1 @ X14 @ X15 @ X16)
% 0.25/0.54           = (k2_xboole_0 @ (k2_tarski @ X14 @ X15) @ (k1_tarski @ X16)))),
% 0.25/0.54      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.25/0.54  thf('18', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.54         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X1 @ X0) @ X2)
% 0.25/0.54           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.25/0.54              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 0.25/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.25/0.54  thf('19', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.25/0.54         ((k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.25/0.54           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.25/0.54           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.25/0.54              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.25/0.54      inference('sup+', [status(thm)], ['11', '18'])).
% 0.25/0.54  thf(l62_enumset1, axiom,
% 0.25/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.25/0.54     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.25/0.54       ( k2_xboole_0 @
% 0.25/0.54         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 0.25/0.54  thf('20', plain,
% 0.25/0.54      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.25/0.54         ((k4_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11)
% 0.25/0.54           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X7 @ X8) @ 
% 0.25/0.54              (k1_enumset1 @ X9 @ X10 @ X11)))),
% 0.25/0.54      inference('cnf', [status(esa)], [l62_enumset1])).
% 0.25/0.54  thf('21', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.25/0.54         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.25/0.54           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.25/0.54              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.25/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.25/0.54  thf('22', plain,
% 0.25/0.54      (((k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.25/0.54         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 0.25/0.54      inference('demod', [status(thm)], ['0', '21'])).
% 0.25/0.54  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.25/0.54  
% 0.25/0.54  % SZS output end Refutation
% 0.25/0.54  
% 0.25/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
