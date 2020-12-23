%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZB8mOg3U8j

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:19 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  242 ( 272 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(t118_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ D @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ C @ D @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t118_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_C @ sk_D @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t116_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ B @ A @ D ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X5 @ X4 @ X3 @ X6 )
      = ( k2_enumset1 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t116_enumset1])).

thf('2',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_D @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf(t53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X8 @ X9 ) @ ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t53_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X8 @ X9 ) @ ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t53_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X0 @ X1 @ X2 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t79_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_enumset1 @ X13 @ X13 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t79_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_enumset1 @ X13 @ X13 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t79_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('13',plain,(
    $false ),
    inference(simplify,[status(thm)],['12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZB8mOg3U8j
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:16:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 19 iterations in 0.014s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.45  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.45  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.45  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.45  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.19/0.45  thf(t118_enumset1, conjecture,
% 0.19/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.45     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ D @ A @ B ) ))).
% 0.19/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.45    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.45        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ D @ A @ B ) ) )),
% 0.19/0.45    inference('cnf.neg', [status(esa)], [t118_enumset1])).
% 0.19/0.45  thf('0', plain,
% 0.19/0.45      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.19/0.45         != (k2_enumset1 @ sk_C @ sk_D @ sk_A @ sk_B))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(t116_enumset1, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.45     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ B @ A @ D ) ))).
% 0.19/0.45  thf('1', plain,
% 0.19/0.45      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.45         ((k2_enumset1 @ X5 @ X4 @ X3 @ X6) = (k2_enumset1 @ X3 @ X4 @ X5 @ X6))),
% 0.19/0.45      inference('cnf', [status(esa)], [t116_enumset1])).
% 0.19/0.45  thf('2', plain,
% 0.19/0.45      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.19/0.45         != (k2_enumset1 @ sk_A @ sk_D @ sk_C @ sk_B))),
% 0.19/0.45      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.45  thf(t102_enumset1, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i]:
% 0.19/0.45     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 0.19/0.45  thf('3', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.45         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.19/0.45      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.19/0.45  thf(t53_enumset1, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.45     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.19/0.45       ( k2_xboole_0 @
% 0.19/0.45         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 0.19/0.45  thf('4', plain,
% 0.19/0.45      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.45         ((k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.19/0.45           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X8 @ X9) @ 
% 0.19/0.45              (k1_enumset1 @ X10 @ X11 @ X12)))),
% 0.19/0.45      inference('cnf', [status(esa)], [t53_enumset1])).
% 0.19/0.45  thf('5', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.45         ((k4_enumset1 @ X5 @ X4 @ X3 @ X0 @ X1 @ X2)
% 0.19/0.45           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.19/0.45              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.19/0.45      inference('sup+', [status(thm)], ['3', '4'])).
% 0.19/0.45  thf('6', plain,
% 0.19/0.45      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.45         ((k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.19/0.45           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X8 @ X9) @ 
% 0.19/0.45              (k1_enumset1 @ X10 @ X11 @ X12)))),
% 0.19/0.45      inference('cnf', [status(esa)], [t53_enumset1])).
% 0.19/0.45  thf('7', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.45         ((k4_enumset1 @ X5 @ X4 @ X3 @ X0 @ X1 @ X2)
% 0.19/0.45           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.19/0.45      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.45  thf(t79_enumset1, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.45     ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D ) =
% 0.19/0.45       ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.19/0.45  thf('8', plain,
% 0.19/0.45      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.45         ((k4_enumset1 @ X13 @ X13 @ X13 @ X14 @ X15 @ X16)
% 0.19/0.45           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 0.19/0.45      inference('cnf', [status(esa)], [t79_enumset1])).
% 0.19/0.45  thf('9', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.45         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.19/0.45           = (k2_enumset1 @ X3 @ X0 @ X1 @ X2))),
% 0.19/0.45      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.45  thf('10', plain,
% 0.19/0.45      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.45         ((k4_enumset1 @ X13 @ X13 @ X13 @ X14 @ X15 @ X16)
% 0.19/0.45           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 0.19/0.45      inference('cnf', [status(esa)], [t79_enumset1])).
% 0.19/0.45  thf('11', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.45         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X0 @ X1 @ X2))),
% 0.19/0.45      inference('sup+', [status(thm)], ['9', '10'])).
% 0.19/0.45  thf('12', plain,
% 0.19/0.45      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.19/0.45         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.19/0.45      inference('demod', [status(thm)], ['2', '11'])).
% 0.19/0.45  thf('13', plain, ($false), inference('simplify', [status(thm)], ['12'])).
% 0.19/0.45  
% 0.19/0.45  % SZS output end Refutation
% 0.19/0.45  
% 0.19/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
