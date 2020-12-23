%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BK5qNnbaqu

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:14 EST 2020

% Result     : Theorem 3.04s
% Output     : Refutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :  265 ( 293 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t25_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_mcart_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
 != ( k2_enumset1 @ ( k4_tarski @ sk_A @ sk_C ) @ ( k4_tarski @ sk_A @ sk_D ) @ ( k4_tarski @ sk_B @ sk_C ) @ ( k4_tarski @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X14 @ X15 ) )
      = ( k2_tarski @ ( k4_tarski @ X13 @ X14 ) @ ( k4_tarski @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X14 @ X15 ) )
      = ( k2_tarski @ ( k4_tarski @ X13 @ X14 ) @ ( k4_tarski @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_enumset1 @ ( k4_tarski @ X2 @ X1 ) @ ( k4_tarski @ X2 @ X0 ) @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X5 @ X3 ) @ ( k4_tarski @ X2 @ X1 ) @ ( k4_tarski @ X2 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X5 ) @ ( k2_tarski @ X4 @ X3 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X9 @ X11 ) @ X10 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X9 @ X10 ) @ ( k2_zfmisc_1 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('8',plain,(
    ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
 != ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','5','6','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BK5qNnbaqu
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:12:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 3.04/3.28  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.04/3.28  % Solved by: fo/fo7.sh
% 3.04/3.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.04/3.28  % done 942 iterations in 2.815s
% 3.04/3.28  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.04/3.28  % SZS output start Refutation
% 3.04/3.28  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 3.04/3.28  thf(sk_D_type, type, sk_D: $i).
% 3.04/3.28  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.04/3.28  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.04/3.28  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.04/3.28  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.04/3.28  thf(sk_A_type, type, sk_A: $i).
% 3.04/3.28  thf(sk_C_type, type, sk_C: $i).
% 3.04/3.28  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.04/3.28  thf(sk_B_type, type, sk_B: $i).
% 3.04/3.28  thf(t25_mcart_1, conjecture,
% 3.04/3.28    (![A:$i,B:$i,C:$i,D:$i]:
% 3.04/3.28     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 3.04/3.28       ( k2_enumset1 @
% 3.04/3.28         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 3.04/3.28         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 3.04/3.28  thf(zf_stmt_0, negated_conjecture,
% 3.04/3.28    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.04/3.28        ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 3.04/3.28          ( k2_enumset1 @
% 3.04/3.28            ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 3.04/3.28            ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )),
% 3.04/3.28    inference('cnf.neg', [status(esa)], [t25_mcart_1])).
% 3.04/3.28  thf('0', plain,
% 3.04/3.28      (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))
% 3.04/3.28         != (k2_enumset1 @ (k4_tarski @ sk_A @ sk_C) @ 
% 3.04/3.28             (k4_tarski @ sk_A @ sk_D) @ (k4_tarski @ sk_B @ sk_C) @ 
% 3.04/3.28             (k4_tarski @ sk_B @ sk_D)))),
% 3.04/3.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.28  thf(t36_zfmisc_1, axiom,
% 3.04/3.28    (![A:$i,B:$i,C:$i]:
% 3.04/3.28     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 3.04/3.28         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 3.04/3.28       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 3.04/3.28         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 3.04/3.28  thf('1', plain,
% 3.04/3.28      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.04/3.28         ((k2_zfmisc_1 @ (k1_tarski @ X13) @ (k2_tarski @ X14 @ X15))
% 3.04/3.28           = (k2_tarski @ (k4_tarski @ X13 @ X14) @ (k4_tarski @ X13 @ X15)))),
% 3.04/3.28      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 3.04/3.28  thf('2', plain,
% 3.04/3.28      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.04/3.28         ((k2_zfmisc_1 @ (k1_tarski @ X13) @ (k2_tarski @ X14 @ X15))
% 3.04/3.28           = (k2_tarski @ (k4_tarski @ X13 @ X14) @ (k4_tarski @ X13 @ X15)))),
% 3.04/3.28      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 3.04/3.28  thf(l53_enumset1, axiom,
% 3.04/3.28    (![A:$i,B:$i,C:$i,D:$i]:
% 3.04/3.28     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 3.04/3.28       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 3.04/3.28  thf('3', plain,
% 3.04/3.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.04/3.28         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 3.04/3.28           = (k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X2 @ X3)))),
% 3.04/3.28      inference('cnf', [status(esa)], [l53_enumset1])).
% 3.04/3.28  thf('4', plain,
% 3.04/3.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.04/3.28         ((k2_enumset1 @ (k4_tarski @ X2 @ X1) @ (k4_tarski @ X2 @ X0) @ X4 @ 
% 3.04/3.28           X3)
% 3.04/3.28           = (k2_xboole_0 @ 
% 3.04/3.28              (k2_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)) @ 
% 3.04/3.28              (k2_tarski @ X4 @ X3)))),
% 3.04/3.28      inference('sup+', [status(thm)], ['2', '3'])).
% 3.04/3.28  thf('5', plain,
% 3.04/3.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 3.04/3.28         ((k2_enumset1 @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X5 @ X3) @ 
% 3.04/3.28           (k4_tarski @ X2 @ X1) @ (k4_tarski @ X2 @ X0))
% 3.04/3.28           = (k2_xboole_0 @ 
% 3.04/3.28              (k2_zfmisc_1 @ (k1_tarski @ X5) @ (k2_tarski @ X4 @ X3)) @ 
% 3.04/3.28              (k2_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))))),
% 3.04/3.28      inference('sup+', [status(thm)], ['1', '4'])).
% 3.04/3.28  thf(t120_zfmisc_1, axiom,
% 3.04/3.28    (![A:$i,B:$i,C:$i]:
% 3.04/3.28     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 3.04/3.28         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 3.04/3.28       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 3.04/3.28         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 3.04/3.28  thf('6', plain,
% 3.04/3.28      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.04/3.28         ((k2_zfmisc_1 @ (k2_xboole_0 @ X9 @ X11) @ X10)
% 3.04/3.28           = (k2_xboole_0 @ (k2_zfmisc_1 @ X9 @ X10) @ 
% 3.04/3.28              (k2_zfmisc_1 @ X11 @ X10)))),
% 3.04/3.28      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 3.04/3.28  thf(t41_enumset1, axiom,
% 3.04/3.28    (![A:$i,B:$i]:
% 3.04/3.28     ( ( k2_tarski @ A @ B ) =
% 3.04/3.28       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 3.04/3.28  thf('7', plain,
% 3.04/3.28      (![X4 : $i, X5 : $i]:
% 3.04/3.28         ((k2_tarski @ X4 @ X5)
% 3.04/3.28           = (k2_xboole_0 @ (k1_tarski @ X4) @ (k1_tarski @ X5)))),
% 3.04/3.28      inference('cnf', [status(esa)], [t41_enumset1])).
% 3.04/3.28  thf('8', plain,
% 3.04/3.28      (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))
% 3.04/3.28         != (k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ 
% 3.04/3.28             (k2_tarski @ sk_C @ sk_D)))),
% 3.04/3.28      inference('demod', [status(thm)], ['0', '5', '6', '7'])).
% 3.04/3.28  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 3.04/3.28  
% 3.04/3.28  % SZS output end Refutation
% 3.04/3.28  
% 3.04/3.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
