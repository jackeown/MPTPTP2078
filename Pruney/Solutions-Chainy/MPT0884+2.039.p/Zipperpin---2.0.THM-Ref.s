%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0ZGjJ4Rrja

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:28 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :  328 ( 366 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t44_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) )
        = ( k2_enumset1 @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) )
      = ( k2_tarski @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ X14 @ X17 ) @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X16 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X14 @ X15 @ X16 ) @ ( k3_mcart_1 @ X17 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t40_mcart_1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ ( k3_mcart_1 @ X3 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ ( k2_tarski @ X3 @ X2 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ X14 @ X17 ) @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X16 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X14 @ X15 @ X16 ) @ ( k3_mcart_1 @ X17 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t40_mcart_1])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t132_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ ( k2_tarski @ X7 @ X9 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X10 @ ( k1_tarski @ X7 ) ) @ ( k2_zfmisc_1 @ X10 @ ( k1_tarski @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[t132_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ ( k1_tarski @ X0 ) ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k1_tarski @ X3 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X1 @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ ( k1_tarski @ X0 ) ) @ ( k3_zfmisc_1 @ X2 @ X1 @ ( k1_tarski @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['0','3','4','10'])).

thf('12',plain,(
    $false ),
    inference(simplify,[status(thm)],['11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0ZGjJ4Rrja
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:48:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 239 iterations in 0.155s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.43/0.62  thf(sk_E_type, type, sk_E: $i).
% 0.43/0.62  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.43/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.43/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.62  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.43/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.62  thf(t44_mcart_1, conjecture,
% 0.43/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.43/0.62     ( ( k3_zfmisc_1 @
% 0.43/0.62         ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 0.43/0.62       ( k2_enumset1 @
% 0.43/0.62         ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 0.43/0.62         ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.43/0.62        ( ( k3_zfmisc_1 @
% 0.43/0.62            ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 0.43/0.62          ( k2_enumset1 @
% 0.43/0.62            ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 0.43/0.62            ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t44_mcart_1])).
% 0.43/0.62  thf('0', plain,
% 0.43/0.62      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 0.43/0.62         (k2_tarski @ sk_D @ sk_E))
% 0.43/0.62         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.43/0.62             (k3_mcart_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62             (k3_mcart_1 @ sk_A @ sk_C @ sk_E) @ 
% 0.43/0.62             (k3_mcart_1 @ sk_B @ sk_C @ sk_E)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(t40_mcart_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.62     ( ( k3_zfmisc_1 @
% 0.43/0.62         ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) =
% 0.43/0.62       ( k2_tarski @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) ) ))).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ (k2_tarski @ X14 @ X17) @ (k1_tarski @ X15) @ 
% 0.43/0.62           (k1_tarski @ X16))
% 0.43/0.62           = (k2_tarski @ (k3_mcart_1 @ X14 @ X15 @ X16) @ 
% 0.43/0.62              (k3_mcart_1 @ X17 @ X15 @ X16)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t40_mcart_1])).
% 0.43/0.62  thf(l53_enumset1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.62     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.43/0.62       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 0.43/0.62           = (k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X2 @ X3)))),
% 0.43/0.62      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.62         ((k2_enumset1 @ (k3_mcart_1 @ X3 @ X1 @ X0) @ 
% 0.43/0.62           (k3_mcart_1 @ X2 @ X1 @ X0) @ X5 @ X4)
% 0.43/0.62           = (k2_xboole_0 @ 
% 0.43/0.62              (k3_zfmisc_1 @ (k2_tarski @ X3 @ X2) @ (k1_tarski @ X1) @ 
% 0.43/0.62               (k1_tarski @ X0)) @ 
% 0.43/0.62              (k2_tarski @ X5 @ X4)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['1', '2'])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ (k2_tarski @ X14 @ X17) @ (k1_tarski @ X15) @ 
% 0.43/0.62           (k1_tarski @ X16))
% 0.43/0.62           = (k2_tarski @ (k3_mcart_1 @ X14 @ X15 @ X16) @ 
% 0.43/0.62              (k3_mcart_1 @ X17 @ X15 @ X16)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t40_mcart_1])).
% 0.43/0.62  thf(d3_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.43/0.62       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.43/0.62  thf('5', plain,
% 0.43/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ X11 @ X12 @ X13)
% 0.43/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13))),
% 0.43/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.43/0.62  thf(t132_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.43/0.62         ( k2_xboole_0 @
% 0.43/0.62           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.43/0.62           ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) ) & 
% 0.43/0.62       ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C ) =
% 0.43/0.62         ( k2_xboole_0 @
% 0.43/0.62           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.43/0.62           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ))).
% 0.43/0.62  thf('6', plain,
% 0.43/0.62      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.43/0.62         ((k2_zfmisc_1 @ X10 @ (k2_tarski @ X7 @ X9))
% 0.43/0.62           = (k2_xboole_0 @ (k2_zfmisc_1 @ X10 @ (k1_tarski @ X7)) @ 
% 0.43/0.62              (k2_zfmisc_1 @ X10 @ (k1_tarski @ X9))))),
% 0.43/0.62      inference('cnf', [status(esa)], [t132_zfmisc_1])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ (k2_tarski @ X0 @ X3))
% 0.43/0.62           = (k2_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ (k1_tarski @ X0)) @ 
% 0.43/0.62              (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ (k1_tarski @ X3))))),
% 0.43/0.62      inference('sup+', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ X11 @ X12 @ X13)
% 0.43/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13))),
% 0.43/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ X11 @ X12 @ X13)
% 0.43/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13))),
% 0.43/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.62         ((k3_zfmisc_1 @ X2 @ X1 @ (k2_tarski @ X0 @ X3))
% 0.43/0.62           = (k2_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ (k1_tarski @ X0)) @ 
% 0.43/0.62              (k3_zfmisc_1 @ X2 @ X1 @ (k1_tarski @ X3))))),
% 0.43/0.62      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.43/0.62  thf('11', plain,
% 0.43/0.62      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 0.43/0.62         (k2_tarski @ sk_D @ sk_E))
% 0.43/0.62         != (k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 0.43/0.62             (k2_tarski @ sk_D @ sk_E)))),
% 0.43/0.62      inference('demod', [status(thm)], ['0', '3', '4', '10'])).
% 0.43/0.62  thf('12', plain, ($false), inference('simplify', [status(thm)], ['11'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.48/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
