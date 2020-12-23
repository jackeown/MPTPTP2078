%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mqL5BhpxPo

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:10 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :  253 ( 281 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t146_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_zfmisc_1])).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X10 ) @ ( k2_tarski @ X11 @ X12 ) )
      = ( k2_tarski @ ( k4_tarski @ X10 @ X11 ) @ ( k4_tarski @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X10 ) @ ( k2_tarski @ X11 @ X12 ) )
      = ( k2_tarski @ ( k4_tarski @ X10 @ X11 ) @ ( k4_tarski @ X10 @ X12 ) ) ) ),
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

thf(t132_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X6 @ X8 ) @ X7 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X7 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X8 ) @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t132_zfmisc_1])).

thf('7',plain,(
    ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
 != ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','5','6'])).

thf('8',plain,(
    $false ),
    inference(simplify,[status(thm)],['7'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mqL5BhpxPo
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:07 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.47/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.67  % Solved by: fo/fo7.sh
% 0.47/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.67  % done 87 iterations in 0.215s
% 0.47/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.67  % SZS output start Refutation
% 0.47/0.67  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.67  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.47/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.67  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.47/0.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.67  thf(t146_zfmisc_1, conjecture,
% 0.47/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 0.47/0.67       ( k2_enumset1 @
% 0.47/0.67         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 0.47/0.67         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 0.47/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.67    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67        ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 0.47/0.67          ( k2_enumset1 @
% 0.47/0.67            ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 0.47/0.67            ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )),
% 0.47/0.67    inference('cnf.neg', [status(esa)], [t146_zfmisc_1])).
% 0.47/0.67  thf('0', plain,
% 0.47/0.67      (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))
% 0.47/0.67         != (k2_enumset1 @ (k4_tarski @ sk_A @ sk_C) @ 
% 0.47/0.67             (k4_tarski @ sk_A @ sk_D) @ (k4_tarski @ sk_B @ sk_C) @ 
% 0.47/0.67             (k4_tarski @ sk_B @ sk_D)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(t36_zfmisc_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.47/0.67         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.47/0.67       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.47/0.67         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.47/0.67  thf('1', plain,
% 0.47/0.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.47/0.67         ((k2_zfmisc_1 @ (k1_tarski @ X10) @ (k2_tarski @ X11 @ X12))
% 0.47/0.67           = (k2_tarski @ (k4_tarski @ X10 @ X11) @ (k4_tarski @ X10 @ X12)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.47/0.67  thf('2', plain,
% 0.47/0.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.47/0.67         ((k2_zfmisc_1 @ (k1_tarski @ X10) @ (k2_tarski @ X11 @ X12))
% 0.47/0.67           = (k2_tarski @ (k4_tarski @ X10 @ X11) @ (k4_tarski @ X10 @ X12)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.47/0.67  thf(l53_enumset1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.67     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.47/0.67       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.47/0.67  thf('3', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.67         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 0.47/0.67           = (k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X2 @ X3)))),
% 0.47/0.67      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.47/0.67  thf('4', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.67         ((k2_enumset1 @ (k4_tarski @ X2 @ X1) @ (k4_tarski @ X2 @ X0) @ X4 @ 
% 0.47/0.67           X3)
% 0.47/0.67           = (k2_xboole_0 @ 
% 0.47/0.67              (k2_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)) @ 
% 0.47/0.67              (k2_tarski @ X4 @ X3)))),
% 0.47/0.67      inference('sup+', [status(thm)], ['2', '3'])).
% 0.47/0.67  thf('5', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.67         ((k2_enumset1 @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X5 @ X3) @ 
% 0.47/0.67           (k4_tarski @ X2 @ X1) @ (k4_tarski @ X2 @ X0))
% 0.47/0.67           = (k2_xboole_0 @ 
% 0.47/0.67              (k2_zfmisc_1 @ (k1_tarski @ X5) @ (k2_tarski @ X4 @ X3)) @ 
% 0.47/0.67              (k2_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))))),
% 0.47/0.67      inference('sup+', [status(thm)], ['1', '4'])).
% 0.47/0.67  thf(t132_zfmisc_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.47/0.67         ( k2_xboole_0 @
% 0.47/0.67           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.47/0.67           ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) ) & 
% 0.47/0.67       ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C ) =
% 0.47/0.67         ( k2_xboole_0 @
% 0.47/0.67           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.47/0.67           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ))).
% 0.47/0.67  thf('6', plain,
% 0.47/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.47/0.67         ((k2_zfmisc_1 @ (k2_tarski @ X6 @ X8) @ X7)
% 0.47/0.67           = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X6) @ X7) @ 
% 0.47/0.67              (k2_zfmisc_1 @ (k1_tarski @ X8) @ X7)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t132_zfmisc_1])).
% 0.47/0.67  thf('7', plain,
% 0.47/0.67      (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))
% 0.47/0.67         != (k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.47/0.67             (k2_tarski @ sk_C @ sk_D)))),
% 0.47/0.67      inference('demod', [status(thm)], ['0', '5', '6'])).
% 0.47/0.67  thf('8', plain, ($false), inference('simplify', [status(thm)], ['7'])).
% 0.47/0.67  
% 0.47/0.67  % SZS output end Refutation
% 0.47/0.67  
% 0.47/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
