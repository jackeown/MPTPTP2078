%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NhQz2KaVHj

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:24 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :  365 ( 429 expanded)
%              Number of equality atoms :   23 (  28 expanded)
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ X16 @ X19 ) @ ( k1_tarski @ X17 ) @ ( k1_tarski @ X18 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X16 @ X17 @ X18 ) @ ( k3_mcart_1 @ X19 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t40_mcart_1])).

thf(t45_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ ( k3_mcart_1 @ X3 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ ( k2_tarski @ X3 @ X2 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ X16 @ X19 ) @ ( k1_tarski @ X17 ) @ ( k1_tarski @ X18 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X16 @ X17 @ X18 ) @ ( k3_mcart_1 @ X19 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t40_mcart_1])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ ( k2_xboole_0 @ X6 @ X8 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X9 @ X6 ) @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ ( k2_zfmisc_1 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X3 ) @ X0 )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X3 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X3 ) @ ( k3_zfmisc_1 @ X2 @ X0 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('14',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_tarski @ sk_E ) )
 != ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_tarski @ sk_E ) ) ),
    inference(demod,[status(thm)],['0','3','4','12','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NhQz2KaVHj
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:26:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.68  % Solved by: fo/fo7.sh
% 0.45/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.68  % done 68 iterations in 0.216s
% 0.45/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.68  % SZS output start Refutation
% 0.45/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.68  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.45/0.68  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.45/0.68  thf(sk_E_type, type, sk_E: $i).
% 0.45/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.68  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.45/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.68  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.68  thf(t43_mcart_1, conjecture,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.45/0.68     ( ( k3_zfmisc_1 @
% 0.45/0.68         ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) @ ( k1_tarski @ E ) ) =
% 0.45/0.68       ( k2_enumset1 @
% 0.45/0.68         ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) @ 
% 0.45/0.68         ( k3_mcart_1 @ A @ D @ E ) @ ( k3_mcart_1 @ B @ D @ E ) ) ))).
% 0.45/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.68    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.45/0.68        ( ( k3_zfmisc_1 @
% 0.45/0.68            ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) @ ( k1_tarski @ E ) ) =
% 0.45/0.68          ( k2_enumset1 @
% 0.45/0.68            ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) @ 
% 0.45/0.68            ( k3_mcart_1 @ A @ D @ E ) @ ( k3_mcart_1 @ B @ D @ E ) ) ) )),
% 0.45/0.68    inference('cnf.neg', [status(esa)], [t43_mcart_1])).
% 0.45/0.68  thf('0', plain,
% 0.45/0.68      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D) @ 
% 0.45/0.68         (k1_tarski @ sk_E))
% 0.45/0.68         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_C @ sk_E) @ 
% 0.45/0.68             (k3_mcart_1 @ sk_B @ sk_C @ sk_E) @ 
% 0.45/0.68             (k3_mcart_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.45/0.68             (k3_mcart_1 @ sk_B @ sk_D @ sk_E)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(t40_mcart_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( k3_zfmisc_1 @
% 0.45/0.68         ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) =
% 0.45/0.68       ( k2_tarski @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) ) ))).
% 0.45/0.68  thf('1', plain,
% 0.45/0.68      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.68         ((k3_zfmisc_1 @ (k2_tarski @ X16 @ X19) @ (k1_tarski @ X17) @ 
% 0.45/0.68           (k1_tarski @ X18))
% 0.45/0.68           = (k2_tarski @ (k3_mcart_1 @ X16 @ X17 @ X18) @ 
% 0.45/0.68              (k3_mcart_1 @ X19 @ X17 @ X18)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t40_mcart_1])).
% 0.45/0.68  thf(t45_enumset1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.45/0.68       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.45/0.68  thf('2', plain,
% 0.45/0.68      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.68         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 0.45/0.68           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t45_enumset1])).
% 0.45/0.68  thf('3', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.68         ((k2_enumset1 @ (k3_mcart_1 @ X3 @ X1 @ X0) @ 
% 0.45/0.68           (k3_mcart_1 @ X2 @ X1 @ X0) @ X5 @ X4)
% 0.45/0.68           = (k2_xboole_0 @ 
% 0.45/0.68              (k3_zfmisc_1 @ (k2_tarski @ X3 @ X2) @ (k1_tarski @ X1) @ 
% 0.45/0.68               (k1_tarski @ X0)) @ 
% 0.45/0.68              (k2_tarski @ X5 @ X4)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['1', '2'])).
% 0.45/0.68  thf('4', plain,
% 0.45/0.68      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.68         ((k3_zfmisc_1 @ (k2_tarski @ X16 @ X19) @ (k1_tarski @ X17) @ 
% 0.45/0.68           (k1_tarski @ X18))
% 0.45/0.68           = (k2_tarski @ (k3_mcart_1 @ X16 @ X17 @ X18) @ 
% 0.45/0.68              (k3_mcart_1 @ X19 @ X17 @ X18)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t40_mcart_1])).
% 0.45/0.68  thf(t120_zfmisc_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.45/0.68         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.45/0.68       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.45/0.68         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.45/0.68  thf('5', plain,
% 0.45/0.68      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.45/0.68         ((k2_zfmisc_1 @ X9 @ (k2_xboole_0 @ X6 @ X8))
% 0.45/0.68           = (k2_xboole_0 @ (k2_zfmisc_1 @ X9 @ X6) @ (k2_zfmisc_1 @ X9 @ X8)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.45/0.68  thf(d3_zfmisc_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.45/0.68       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.45/0.68  thf('6', plain,
% 0.45/0.68      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.68         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.45/0.68           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.45/0.68  thf('7', plain,
% 0.45/0.68      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.68         ((k2_zfmisc_1 @ (k2_xboole_0 @ X6 @ X8) @ X7)
% 0.45/0.68           = (k2_xboole_0 @ (k2_zfmisc_1 @ X6 @ X7) @ (k2_zfmisc_1 @ X8 @ X7)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.45/0.68  thf('8', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.68         ((k2_zfmisc_1 @ (k2_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ X3) @ X0)
% 0.45/0.68           = (k2_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ 
% 0.45/0.68              (k2_zfmisc_1 @ X3 @ X0)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.45/0.68  thf('9', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.68         ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 0.45/0.68           = (k2_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X3) @ 
% 0.45/0.68              (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0) @ X3)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['5', '8'])).
% 0.45/0.68  thf('10', plain,
% 0.45/0.68      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.68         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.45/0.68           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.45/0.68  thf('11', plain,
% 0.45/0.68      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.68         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.45/0.68           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.45/0.68  thf('12', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.68         ((k3_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ X0) @ X3)
% 0.45/0.68           = (k2_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X3) @ 
% 0.45/0.68              (k3_zfmisc_1 @ X2 @ X0 @ X3)))),
% 0.45/0.68      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.45/0.68  thf(t41_enumset1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( k2_tarski @ A @ B ) =
% 0.45/0.68       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.45/0.68  thf('13', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         ((k2_tarski @ X0 @ X1)
% 0.45/0.68           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.45/0.68  thf('14', plain,
% 0.45/0.68      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D) @ 
% 0.45/0.68         (k1_tarski @ sk_E))
% 0.45/0.68         != (k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.45/0.68             (k2_tarski @ sk_C @ sk_D) @ (k1_tarski @ sk_E)))),
% 0.45/0.68      inference('demod', [status(thm)], ['0', '3', '4', '12', '13'])).
% 0.45/0.68  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.45/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
