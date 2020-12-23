%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G3NkV1QORI

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:23 EST 2020

% Result     : Theorem 40.17s
% Output     : Refutation 40.17s
% Verified   : 
% Statistics : Number of formulae       :   41 (  46 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :  443 ( 514 expanded)
%              Number of equality atoms :   29 (  35 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t43_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) @ ( k1_tarski @ E ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) @ ( k3_mcart_1 @ A @ D @ E ) @ ( k3_mcart_1 @ B @ D @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) @ ( k1_tarski @ E ) )
        = ( k2_enumset1 @ ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) @ ( k3_mcart_1 @ A @ D @ E ) @ ( k3_mcart_1 @ B @ D @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_tarski @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_E ) @ ( k3_mcart_1 @ sk_A @ sk_D @ sk_E ) @ ( k3_mcart_1 @ sk_B @ sk_D @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) )
      = ( k2_tarski @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ X18 @ X21 ) @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X20 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X18 @ X19 @ X20 ) @ ( k3_mcart_1 @ X21 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t40_mcart_1])).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ X18 @ X21 ) @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X20 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X18 @ X19 @ X20 ) @ ( k3_mcart_1 @ X21 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t40_mcart_1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ ( k3_mcart_1 @ X3 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ ( k2_tarski @ X3 @ X2 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ ( k3_mcart_1 @ X7 @ X5 @ X4 ) @ ( k3_mcart_1 @ X6 @ X5 @ X4 ) @ ( k3_mcart_1 @ X3 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ ( k2_tarski @ X7 @ X6 ) @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X4 ) ) @ ( k3_zfmisc_1 @ ( k2_tarski @ X3 @ X2 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ ( k2_xboole_0 @ X8 @ X10 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X11 @ X8 ) @ ( k2_zfmisc_1 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) )
      = ( k2_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X3 ) @ X0 )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X0 @ X3 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('14',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X0 @ X3 ) @ ( k3_zfmisc_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_tarski @ sk_E ) )
 != ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_tarski @ sk_E ) ) ),
    inference(demod,[status(thm)],['0','5','15','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G3NkV1QORI
% 0.15/0.34  % Computer   : n002.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:53:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 40.17/40.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 40.17/40.34  % Solved by: fo/fo7.sh
% 40.17/40.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 40.17/40.34  % done 4628 iterations in 39.856s
% 40.17/40.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 40.17/40.34  % SZS output start Refutation
% 40.17/40.34  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 40.17/40.34  thf(sk_C_type, type, sk_C: $i).
% 40.17/40.34  thf(sk_B_type, type, sk_B: $i).
% 40.17/40.34  thf(sk_E_type, type, sk_E: $i).
% 40.17/40.34  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 40.17/40.34  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 40.17/40.34  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 40.17/40.34  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 40.17/40.34  thf(sk_D_type, type, sk_D: $i).
% 40.17/40.34  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 40.17/40.34  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 40.17/40.34  thf(sk_A_type, type, sk_A: $i).
% 40.17/40.34  thf(t43_mcart_1, conjecture,
% 40.17/40.34    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 40.17/40.34     ( ( k3_zfmisc_1 @
% 40.17/40.34         ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) @ ( k1_tarski @ E ) ) =
% 40.17/40.34       ( k2_enumset1 @
% 40.17/40.34         ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) @ 
% 40.17/40.34         ( k3_mcart_1 @ A @ D @ E ) @ ( k3_mcart_1 @ B @ D @ E ) ) ))).
% 40.17/40.34  thf(zf_stmt_0, negated_conjecture,
% 40.17/40.34    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 40.17/40.34        ( ( k3_zfmisc_1 @
% 40.17/40.34            ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) @ ( k1_tarski @ E ) ) =
% 40.17/40.34          ( k2_enumset1 @
% 40.17/40.34            ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) @ 
% 40.17/40.34            ( k3_mcart_1 @ A @ D @ E ) @ ( k3_mcart_1 @ B @ D @ E ) ) ) )),
% 40.17/40.34    inference('cnf.neg', [status(esa)], [t43_mcart_1])).
% 40.17/40.34  thf('0', plain,
% 40.17/40.34      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D) @ 
% 40.17/40.34         (k1_tarski @ sk_E))
% 40.17/40.34         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_C @ sk_E) @ 
% 40.17/40.34             (k3_mcart_1 @ sk_B @ sk_C @ sk_E) @ 
% 40.17/40.34             (k3_mcart_1 @ sk_A @ sk_D @ sk_E) @ 
% 40.17/40.34             (k3_mcart_1 @ sk_B @ sk_D @ sk_E)))),
% 40.17/40.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 40.17/40.34  thf(t40_mcart_1, axiom,
% 40.17/40.34    (![A:$i,B:$i,C:$i,D:$i]:
% 40.17/40.34     ( ( k3_zfmisc_1 @
% 40.17/40.34         ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) =
% 40.17/40.34       ( k2_tarski @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) ) ))).
% 40.17/40.34  thf('1', plain,
% 40.17/40.34      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 40.17/40.34         ((k3_zfmisc_1 @ (k2_tarski @ X18 @ X21) @ (k1_tarski @ X19) @ 
% 40.17/40.34           (k1_tarski @ X20))
% 40.17/40.34           = (k2_tarski @ (k3_mcart_1 @ X18 @ X19 @ X20) @ 
% 40.17/40.34              (k3_mcart_1 @ X21 @ X19 @ X20)))),
% 40.17/40.34      inference('cnf', [status(esa)], [t40_mcart_1])).
% 40.17/40.34  thf('2', plain,
% 40.17/40.34      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 40.17/40.34         ((k3_zfmisc_1 @ (k2_tarski @ X18 @ X21) @ (k1_tarski @ X19) @ 
% 40.17/40.34           (k1_tarski @ X20))
% 40.17/40.34           = (k2_tarski @ (k3_mcart_1 @ X18 @ X19 @ X20) @ 
% 40.17/40.34              (k3_mcart_1 @ X21 @ X19 @ X20)))),
% 40.17/40.34      inference('cnf', [status(esa)], [t40_mcart_1])).
% 40.17/40.34  thf(l53_enumset1, axiom,
% 40.17/40.34    (![A:$i,B:$i,C:$i,D:$i]:
% 40.17/40.34     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 40.17/40.34       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 40.17/40.34  thf('3', plain,
% 40.17/40.34      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 40.17/40.34         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 40.17/40.34           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 40.17/40.34      inference('cnf', [status(esa)], [l53_enumset1])).
% 40.17/40.34  thf('4', plain,
% 40.17/40.34      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 40.17/40.34         ((k2_enumset1 @ (k3_mcart_1 @ X3 @ X1 @ X0) @ 
% 40.17/40.34           (k3_mcart_1 @ X2 @ X1 @ X0) @ X5 @ X4)
% 40.17/40.34           = (k2_xboole_0 @ 
% 40.17/40.34              (k3_zfmisc_1 @ (k2_tarski @ X3 @ X2) @ (k1_tarski @ X1) @ 
% 40.17/40.34               (k1_tarski @ X0)) @ 
% 40.17/40.34              (k2_tarski @ X5 @ X4)))),
% 40.17/40.34      inference('sup+', [status(thm)], ['2', '3'])).
% 40.17/40.34  thf('5', plain,
% 40.17/40.34      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 40.17/40.34         ((k2_enumset1 @ (k3_mcart_1 @ X7 @ X5 @ X4) @ 
% 40.17/40.34           (k3_mcart_1 @ X6 @ X5 @ X4) @ (k3_mcart_1 @ X3 @ X1 @ X0) @ 
% 40.17/40.34           (k3_mcart_1 @ X2 @ X1 @ X0))
% 40.17/40.34           = (k2_xboole_0 @ 
% 40.17/40.34              (k3_zfmisc_1 @ (k2_tarski @ X7 @ X6) @ (k1_tarski @ X5) @ 
% 40.17/40.34               (k1_tarski @ X4)) @ 
% 40.17/40.34              (k3_zfmisc_1 @ (k2_tarski @ X3 @ X2) @ (k1_tarski @ X1) @ 
% 40.17/40.34               (k1_tarski @ X0))))),
% 40.17/40.34      inference('sup+', [status(thm)], ['1', '4'])).
% 40.17/40.34  thf(t120_zfmisc_1, axiom,
% 40.17/40.34    (![A:$i,B:$i,C:$i]:
% 40.17/40.34     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 40.17/40.34         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 40.17/40.34       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 40.17/40.34         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 40.17/40.34  thf('6', plain,
% 40.17/40.34      (![X8 : $i, X10 : $i, X11 : $i]:
% 40.17/40.34         ((k2_zfmisc_1 @ X11 @ (k2_xboole_0 @ X8 @ X10))
% 40.17/40.34           = (k2_xboole_0 @ (k2_zfmisc_1 @ X11 @ X8) @ 
% 40.17/40.34              (k2_zfmisc_1 @ X11 @ X10)))),
% 40.17/40.34      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 40.17/40.34  thf(commutativity_k2_xboole_0, axiom,
% 40.17/40.34    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 40.17/40.34  thf('7', plain,
% 40.17/40.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 40.17/40.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 40.17/40.34  thf('8', plain,
% 40.17/40.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 40.17/40.34         ((k2_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X2 @ X1))
% 40.17/40.34           = (k2_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 40.17/40.34      inference('sup+', [status(thm)], ['6', '7'])).
% 40.17/40.34  thf(d3_zfmisc_1, axiom,
% 40.17/40.34    (![A:$i,B:$i,C:$i]:
% 40.17/40.34     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 40.17/40.34       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 40.17/40.34  thf('9', plain,
% 40.17/40.34      (![X15 : $i, X16 : $i, X17 : $i]:
% 40.17/40.34         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 40.17/40.34           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 40.17/40.34      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 40.17/40.34  thf('10', plain,
% 40.17/40.34      (![X8 : $i, X9 : $i, X10 : $i]:
% 40.17/40.34         ((k2_zfmisc_1 @ (k2_xboole_0 @ X8 @ X10) @ X9)
% 40.17/40.34           = (k2_xboole_0 @ (k2_zfmisc_1 @ X8 @ X9) @ (k2_zfmisc_1 @ X10 @ X9)))),
% 40.17/40.34      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 40.17/40.34  thf('11', plain,
% 40.17/40.34      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 40.17/40.34         ((k2_zfmisc_1 @ (k2_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ X3) @ X0)
% 40.17/40.34           = (k2_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ 
% 40.17/40.34              (k2_zfmisc_1 @ X3 @ X0)))),
% 40.17/40.34      inference('sup+', [status(thm)], ['9', '10'])).
% 40.17/40.34  thf('12', plain,
% 40.17/40.34      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 40.17/40.34         ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 40.17/40.34           = (k2_xboole_0 @ (k3_zfmisc_1 @ X2 @ X0 @ X3) @ 
% 40.17/40.34              (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X3)))),
% 40.17/40.34      inference('sup+', [status(thm)], ['8', '11'])).
% 40.17/40.34  thf('13', plain,
% 40.17/40.34      (![X15 : $i, X16 : $i, X17 : $i]:
% 40.17/40.34         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 40.17/40.34           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 40.17/40.34      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 40.17/40.34  thf('14', plain,
% 40.17/40.34      (![X15 : $i, X16 : $i, X17 : $i]:
% 40.17/40.34         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 40.17/40.34           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 40.17/40.34      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 40.17/40.34  thf('15', plain,
% 40.17/40.34      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 40.17/40.34         ((k3_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ X0) @ X3)
% 40.17/40.34           = (k2_xboole_0 @ (k3_zfmisc_1 @ X2 @ X0 @ X3) @ 
% 40.17/40.34              (k3_zfmisc_1 @ X2 @ X1 @ X3)))),
% 40.17/40.34      inference('demod', [status(thm)], ['12', '13', '14'])).
% 40.17/40.34  thf(t41_enumset1, axiom,
% 40.17/40.34    (![A:$i,B:$i]:
% 40.17/40.34     ( ( k2_tarski @ A @ B ) =
% 40.17/40.34       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 40.17/40.34  thf('16', plain,
% 40.17/40.34      (![X6 : $i, X7 : $i]:
% 40.17/40.34         ((k2_tarski @ X6 @ X7)
% 40.17/40.34           = (k2_xboole_0 @ (k1_tarski @ X6) @ (k1_tarski @ X7)))),
% 40.17/40.34      inference('cnf', [status(esa)], [t41_enumset1])).
% 40.17/40.34  thf('17', plain,
% 40.17/40.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 40.17/40.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 40.17/40.34  thf('18', plain,
% 40.17/40.34      (![X0 : $i, X1 : $i]:
% 40.17/40.34         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 40.17/40.34           = (k2_tarski @ X1 @ X0))),
% 40.17/40.34      inference('sup+', [status(thm)], ['16', '17'])).
% 40.17/40.34  thf('19', plain,
% 40.17/40.34      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D) @ 
% 40.17/40.34         (k1_tarski @ sk_E))
% 40.17/40.34         != (k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ 
% 40.17/40.34             (k2_tarski @ sk_C @ sk_D) @ (k1_tarski @ sk_E)))),
% 40.17/40.34      inference('demod', [status(thm)], ['0', '5', '15', '18'])).
% 40.17/40.34  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 40.17/40.34  
% 40.17/40.34  % SZS output end Refutation
% 40.17/40.34  
% 40.17/40.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
