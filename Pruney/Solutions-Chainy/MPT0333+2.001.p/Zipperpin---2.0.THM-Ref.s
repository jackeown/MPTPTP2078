%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S7oVxrEzB0

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:09 EST 2020

% Result     : Theorem 31.96s
% Output     : Refutation 31.96s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :  253 ( 281 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C_1 @ sk_D ) )
 != ( k2_enumset1 @ ( k4_tarski @ sk_A @ sk_C_1 ) @ ( k4_tarski @ sk_A @ sk_D ) @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k4_tarski @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('1',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X48 ) @ ( k2_tarski @ X49 @ X50 ) )
      = ( k2_tarski @ ( k4_tarski @ X48 @ X49 ) @ ( k4_tarski @ X48 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('2',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X48 ) @ ( k2_tarski @ X49 @ X50 ) )
      = ( k2_tarski @ ( k4_tarski @ X48 @ X49 ) @ ( k4_tarski @ X48 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k2_tarski @ X28 @ X29 ) @ ( k2_tarski @ X30 @ X31 ) ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X39 @ X41 ) @ X40 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X39 ) @ X40 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X41 ) @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t132_zfmisc_1])).

thf('7',plain,(
    ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C_1 @ sk_D ) )
 != ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','5','6'])).

thf('8',plain,(
    $false ),
    inference(simplify,[status(thm)],['7'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S7oVxrEzB0
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:33:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 31.96/32.15  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 31.96/32.15  % Solved by: fo/fo7.sh
% 31.96/32.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 31.96/32.15  % done 28625 iterations in 31.697s
% 31.96/32.15  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 31.96/32.15  % SZS output start Refutation
% 31.96/32.15  thf(sk_B_type, type, sk_B: $i).
% 31.96/32.15  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 31.96/32.15  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 31.96/32.15  thf(sk_D_type, type, sk_D: $i).
% 31.96/32.15  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 31.96/32.15  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 31.96/32.15  thf(sk_C_1_type, type, sk_C_1: $i).
% 31.96/32.15  thf(sk_A_type, type, sk_A: $i).
% 31.96/32.15  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 31.96/32.15  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 31.96/32.15  thf(t146_zfmisc_1, conjecture,
% 31.96/32.15    (![A:$i,B:$i,C:$i,D:$i]:
% 31.96/32.15     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 31.96/32.15       ( k2_enumset1 @
% 31.96/32.15         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 31.96/32.15         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 31.96/32.15  thf(zf_stmt_0, negated_conjecture,
% 31.96/32.15    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 31.96/32.15        ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 31.96/32.15          ( k2_enumset1 @
% 31.96/32.15            ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 31.96/32.15            ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )),
% 31.96/32.15    inference('cnf.neg', [status(esa)], [t146_zfmisc_1])).
% 31.96/32.15  thf('0', plain,
% 31.96/32.15      (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C_1 @ sk_D))
% 31.96/32.15         != (k2_enumset1 @ (k4_tarski @ sk_A @ sk_C_1) @ 
% 31.96/32.15             (k4_tarski @ sk_A @ sk_D) @ (k4_tarski @ sk_B @ sk_C_1) @ 
% 31.96/32.15             (k4_tarski @ sk_B @ sk_D)))),
% 31.96/32.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.96/32.15  thf(t36_zfmisc_1, axiom,
% 31.96/32.15    (![A:$i,B:$i,C:$i]:
% 31.96/32.15     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 31.96/32.15         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 31.96/32.15       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 31.96/32.15         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 31.96/32.15  thf('1', plain,
% 31.96/32.15      (![X48 : $i, X49 : $i, X50 : $i]:
% 31.96/32.15         ((k2_zfmisc_1 @ (k1_tarski @ X48) @ (k2_tarski @ X49 @ X50))
% 31.96/32.15           = (k2_tarski @ (k4_tarski @ X48 @ X49) @ (k4_tarski @ X48 @ X50)))),
% 31.96/32.15      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 31.96/32.15  thf('2', plain,
% 31.96/32.15      (![X48 : $i, X49 : $i, X50 : $i]:
% 31.96/32.15         ((k2_zfmisc_1 @ (k1_tarski @ X48) @ (k2_tarski @ X49 @ X50))
% 31.96/32.15           = (k2_tarski @ (k4_tarski @ X48 @ X49) @ (k4_tarski @ X48 @ X50)))),
% 31.96/32.15      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 31.96/32.15  thf(l53_enumset1, axiom,
% 31.96/32.15    (![A:$i,B:$i,C:$i,D:$i]:
% 31.96/32.15     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 31.96/32.15       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 31.96/32.15  thf('3', plain,
% 31.96/32.15      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 31.96/32.15         ((k2_enumset1 @ X28 @ X29 @ X30 @ X31)
% 31.96/32.15           = (k2_xboole_0 @ (k2_tarski @ X28 @ X29) @ (k2_tarski @ X30 @ X31)))),
% 31.96/32.15      inference('cnf', [status(esa)], [l53_enumset1])).
% 31.96/32.15  thf('4', plain,
% 31.96/32.15      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 31.96/32.15         ((k2_enumset1 @ (k4_tarski @ X2 @ X1) @ (k4_tarski @ X2 @ X0) @ X4 @ 
% 31.96/32.15           X3)
% 31.96/32.15           = (k2_xboole_0 @ 
% 31.96/32.15              (k2_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)) @ 
% 31.96/32.15              (k2_tarski @ X4 @ X3)))),
% 31.96/32.15      inference('sup+', [status(thm)], ['2', '3'])).
% 31.96/32.15  thf('5', plain,
% 31.96/32.15      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 31.96/32.15         ((k2_enumset1 @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X5 @ X3) @ 
% 31.96/32.15           (k4_tarski @ X2 @ X1) @ (k4_tarski @ X2 @ X0))
% 31.96/32.15           = (k2_xboole_0 @ 
% 31.96/32.15              (k2_zfmisc_1 @ (k1_tarski @ X5) @ (k2_tarski @ X4 @ X3)) @ 
% 31.96/32.15              (k2_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))))),
% 31.96/32.15      inference('sup+', [status(thm)], ['1', '4'])).
% 31.96/32.15  thf(t132_zfmisc_1, axiom,
% 31.96/32.15    (![A:$i,B:$i,C:$i]:
% 31.96/32.15     ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 31.96/32.15         ( k2_xboole_0 @
% 31.96/32.15           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 31.96/32.15           ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) ) & 
% 31.96/32.15       ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C ) =
% 31.96/32.15         ( k2_xboole_0 @
% 31.96/32.15           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 31.96/32.15           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ))).
% 31.96/32.15  thf('6', plain,
% 31.96/32.15      (![X39 : $i, X40 : $i, X41 : $i]:
% 31.96/32.15         ((k2_zfmisc_1 @ (k2_tarski @ X39 @ X41) @ X40)
% 31.96/32.15           = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X39) @ X40) @ 
% 31.96/32.15              (k2_zfmisc_1 @ (k1_tarski @ X41) @ X40)))),
% 31.96/32.15      inference('cnf', [status(esa)], [t132_zfmisc_1])).
% 31.96/32.15  thf('7', plain,
% 31.96/32.15      (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C_1 @ sk_D))
% 31.96/32.15         != (k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ 
% 31.96/32.15             (k2_tarski @ sk_C_1 @ sk_D)))),
% 31.96/32.15      inference('demod', [status(thm)], ['0', '5', '6'])).
% 31.96/32.15  thf('8', plain, ($false), inference('simplify', [status(thm)], ['7'])).
% 31.96/32.15  
% 31.96/32.15  % SZS output end Refutation
% 31.96/32.15  
% 31.96/32.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
