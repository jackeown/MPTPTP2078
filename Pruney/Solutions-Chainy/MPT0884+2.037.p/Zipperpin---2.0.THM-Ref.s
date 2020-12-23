%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ax5E7d038x

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:28 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  383 ( 421 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ X16 @ X19 ) @ ( k1_tarski @ X17 ) @ ( k1_tarski @ X18 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X16 @ X17 @ X18 ) @ ( k3_mcart_1 @ X19 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t40_mcart_1])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t132_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ ( k2_tarski @ X6 @ X8 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X9 @ ( k1_tarski @ X6 ) ) @ ( k2_zfmisc_1 @ X9 @ ( k1_tarski @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[t132_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ ( k1_tarski @ X0 ) ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k1_tarski @ X3 ) ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X1 @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ ( k1_tarski @ X0 ) ) @ ( k3_zfmisc_1 @ X2 @ X1 @ ( k1_tarski @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ X3 @ X2 ) @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X4 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ ( k3_mcart_1 @ X3 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) @ ( k3_zfmisc_1 @ ( k2_tarski @ X3 @ X2 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X4 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ X16 @ X19 ) @ ( k1_tarski @ X17 ) @ ( k1_tarski @ X18 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X16 @ X17 @ X18 ) @ ( k3_mcart_1 @ X19 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t40_mcart_1])).

thf(t45_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X5 @ X4 @ ( k3_mcart_1 @ X3 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k3_zfmisc_1 @ ( k2_tarski @ X3 @ X2 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_enumset1 @ ( k3_mcart_1 @ X4 @ X2 @ X1 ) @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) @ ( k3_mcart_1 @ X4 @ X2 @ X0 ) @ ( k3_mcart_1 @ X3 @ X2 @ X0 ) )
      = ( k3_zfmisc_1 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['0','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ax5E7d038x
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:47:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 122 iterations in 0.212s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.67  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.46/0.67  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.46/0.67  thf(sk_E_type, type, sk_E: $i).
% 0.46/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.67  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.46/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.67  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.67  thf(t44_mcart_1, conjecture,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.46/0.67     ( ( k3_zfmisc_1 @
% 0.46/0.67         ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 0.46/0.67       ( k2_enumset1 @
% 0.46/0.67         ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 0.46/0.67         ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.46/0.67        ( ( k3_zfmisc_1 @
% 0.46/0.67            ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 0.46/0.67          ( k2_enumset1 @
% 0.46/0.67            ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 0.46/0.67            ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t44_mcart_1])).
% 0.46/0.67  thf('0', plain,
% 0.46/0.67      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 0.46/0.67         (k2_tarski @ sk_D @ sk_E))
% 0.46/0.67         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.46/0.67             (k3_mcart_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.46/0.67             (k3_mcart_1 @ sk_A @ sk_C @ sk_E) @ 
% 0.46/0.67             (k3_mcart_1 @ sk_B @ sk_C @ sk_E)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(t40_mcart_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67     ( ( k3_zfmisc_1 @
% 0.46/0.67         ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) =
% 0.46/0.67       ( k2_tarski @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) ) ))).
% 0.46/0.67  thf('1', plain,
% 0.46/0.67      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.67         ((k3_zfmisc_1 @ (k2_tarski @ X16 @ X19) @ (k1_tarski @ X17) @ 
% 0.46/0.67           (k1_tarski @ X18))
% 0.46/0.67           = (k2_tarski @ (k3_mcart_1 @ X16 @ X17 @ X18) @ 
% 0.46/0.67              (k3_mcart_1 @ X19 @ X17 @ X18)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t40_mcart_1])).
% 0.46/0.67  thf(d3_zfmisc_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.46/0.67       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.46/0.67  thf('2', plain,
% 0.46/0.67      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.67         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.46/0.67           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.46/0.67  thf(t132_zfmisc_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.46/0.67         ( k2_xboole_0 @
% 0.46/0.67           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 0.46/0.67           ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) ) & 
% 0.46/0.67       ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C ) =
% 0.46/0.67         ( k2_xboole_0 @
% 0.46/0.67           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 0.46/0.67           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ))).
% 0.46/0.67  thf('3', plain,
% 0.46/0.67      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.46/0.67         ((k2_zfmisc_1 @ X9 @ (k2_tarski @ X6 @ X8))
% 0.46/0.67           = (k2_xboole_0 @ (k2_zfmisc_1 @ X9 @ (k1_tarski @ X6)) @ 
% 0.46/0.67              (k2_zfmisc_1 @ X9 @ (k1_tarski @ X8))))),
% 0.46/0.67      inference('cnf', [status(esa)], [t132_zfmisc_1])).
% 0.46/0.67  thf('4', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.67         ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ (k2_tarski @ X0 @ X3))
% 0.46/0.67           = (k2_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ (k1_tarski @ X0)) @ 
% 0.46/0.67              (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ (k1_tarski @ X3))))),
% 0.46/0.67      inference('sup+', [status(thm)], ['2', '3'])).
% 0.46/0.67  thf('5', plain,
% 0.46/0.67      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.67         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.46/0.67           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.46/0.67  thf('6', plain,
% 0.46/0.67      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.67         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.46/0.67           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.46/0.67  thf('7', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.67         ((k3_zfmisc_1 @ X2 @ X1 @ (k2_tarski @ X0 @ X3))
% 0.46/0.67           = (k2_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ (k1_tarski @ X0)) @ 
% 0.46/0.67              (k3_zfmisc_1 @ X2 @ X1 @ (k1_tarski @ X3))))),
% 0.46/0.67      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.46/0.67  thf('8', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.67         ((k3_zfmisc_1 @ (k2_tarski @ X3 @ X2) @ (k1_tarski @ X1) @ 
% 0.46/0.67           (k2_tarski @ X0 @ X4))
% 0.46/0.67           = (k2_xboole_0 @ 
% 0.46/0.67              (k2_tarski @ (k3_mcart_1 @ X3 @ X1 @ X0) @ 
% 0.46/0.67               (k3_mcart_1 @ X2 @ X1 @ X0)) @ 
% 0.46/0.67              (k3_zfmisc_1 @ (k2_tarski @ X3 @ X2) @ (k1_tarski @ X1) @ 
% 0.46/0.67               (k1_tarski @ X4))))),
% 0.46/0.67      inference('sup+', [status(thm)], ['1', '7'])).
% 0.46/0.67  thf('9', plain,
% 0.46/0.67      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.67         ((k3_zfmisc_1 @ (k2_tarski @ X16 @ X19) @ (k1_tarski @ X17) @ 
% 0.46/0.67           (k1_tarski @ X18))
% 0.46/0.67           = (k2_tarski @ (k3_mcart_1 @ X16 @ X17 @ X18) @ 
% 0.46/0.67              (k3_mcart_1 @ X19 @ X17 @ X18)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t40_mcart_1])).
% 0.46/0.67  thf(t45_enumset1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.46/0.67       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.46/0.67  thf('10', plain,
% 0.46/0.67      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.67         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 0.46/0.67           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t45_enumset1])).
% 0.46/0.67  thf('11', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.67         ((k2_enumset1 @ X5 @ X4 @ (k3_mcart_1 @ X3 @ X1 @ X0) @ 
% 0.46/0.67           (k3_mcart_1 @ X2 @ X1 @ X0))
% 0.46/0.67           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.46/0.67              (k3_zfmisc_1 @ (k2_tarski @ X3 @ X2) @ (k1_tarski @ X1) @ 
% 0.46/0.67               (k1_tarski @ X0))))),
% 0.46/0.67      inference('sup+', [status(thm)], ['9', '10'])).
% 0.46/0.67  thf('12', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.67         ((k2_enumset1 @ (k3_mcart_1 @ X4 @ X2 @ X1) @ 
% 0.46/0.67           (k3_mcart_1 @ X3 @ X2 @ X1) @ (k3_mcart_1 @ X4 @ X2 @ X0) @ 
% 0.46/0.67           (k3_mcart_1 @ X3 @ X2 @ X0))
% 0.46/0.67           = (k3_zfmisc_1 @ (k2_tarski @ X4 @ X3) @ (k1_tarski @ X2) @ 
% 0.46/0.67              (k2_tarski @ X1 @ X0)))),
% 0.46/0.67      inference('sup+', [status(thm)], ['8', '11'])).
% 0.46/0.67  thf('13', plain,
% 0.46/0.67      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 0.46/0.67         (k2_tarski @ sk_D @ sk_E))
% 0.46/0.67         != (k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 0.46/0.67             (k2_tarski @ sk_D @ sk_E)))),
% 0.46/0.67      inference('demod', [status(thm)], ['0', '12'])).
% 0.46/0.67  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
