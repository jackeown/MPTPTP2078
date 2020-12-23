%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lNcdCNoKyo

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:28 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :  414 ( 444 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

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

thf(t104_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X3 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('2',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_mcart_1 @ X15 @ X16 @ X17 )
      = ( k4_tarski @ ( k4_tarski @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_mcart_1 @ X15 @ X16 @ X17 )
      = ( k4_tarski @ ( k4_tarski @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t146_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X7 @ X10 ) @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_enumset1 @ ( k4_tarski @ X7 @ X8 ) @ ( k4_tarski @ X7 @ X9 ) @ ( k4_tarski @ X10 @ X8 ) @ ( k4_tarski @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t146_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_mcart_1 @ X15 @ X16 @ X17 )
      = ( k4_tarski @ ( k4_tarski @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X4 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) @ ( k4_tarski @ X4 @ X0 ) @ ( k4_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_mcart_1 @ X15 @ X16 @ X17 )
      = ( k4_tarski @ ( k4_tarski @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X5 @ X4 ) @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ X5 @ X4 @ X0 ) @ ( k3_mcart_1 @ X5 @ X4 @ X3 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X11 @ X12 ) @ ( k1_tarski @ X14 ) )
      = ( k2_tarski @ ( k4_tarski @ X11 @ X14 ) @ ( k4_tarski @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_zfmisc_1 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('14',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['2','11','12','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lNcdCNoKyo
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 132 iterations in 0.113s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.38/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.57  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.38/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.57  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.57  thf(t44_mcart_1, conjecture,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.38/0.57     ( ( k3_zfmisc_1 @
% 0.38/0.57         ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 0.38/0.57       ( k2_enumset1 @
% 0.38/0.57         ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 0.38/0.57         ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.38/0.57        ( ( k3_zfmisc_1 @
% 0.38/0.57            ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k2_tarski @ D @ E ) ) =
% 0.38/0.57          ( k2_enumset1 @
% 0.38/0.57            ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) @ 
% 0.38/0.57            ( k3_mcart_1 @ A @ C @ E ) @ ( k3_mcart_1 @ B @ C @ E ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t44_mcart_1])).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 0.38/0.57         (k2_tarski @ sk_D @ sk_E))
% 0.38/0.57         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.38/0.57             (k3_mcart_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.57             (k3_mcart_1 @ sk_A @ sk_C @ sk_E) @ 
% 0.38/0.57             (k3_mcart_1 @ sk_B @ sk_C @ sk_E)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(t104_enumset1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.57         ((k2_enumset1 @ X0 @ X2 @ X1 @ X3) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [t104_enumset1])).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 0.38/0.57         (k2_tarski @ sk_D @ sk_E))
% 0.38/0.57         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.38/0.57             (k3_mcart_1 @ sk_A @ sk_C @ sk_E) @ 
% 0.38/0.57             (k3_mcart_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.38/0.57             (k3_mcart_1 @ sk_B @ sk_C @ sk_E)))),
% 0.38/0.57      inference('demod', [status(thm)], ['0', '1'])).
% 0.38/0.57  thf(d3_mcart_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.57         ((k3_mcart_1 @ X15 @ X16 @ X17)
% 0.38/0.57           = (k4_tarski @ (k4_tarski @ X15 @ X16) @ X17))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.57         ((k3_mcart_1 @ X15 @ X16 @ X17)
% 0.38/0.57           = (k4_tarski @ (k4_tarski @ X15 @ X16) @ X17))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.38/0.57  thf(t146_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 0.38/0.57       ( k2_enumset1 @
% 0.38/0.57         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 0.38/0.57         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.57         ((k2_zfmisc_1 @ (k2_tarski @ X7 @ X10) @ (k2_tarski @ X8 @ X9))
% 0.38/0.57           = (k2_enumset1 @ (k4_tarski @ X7 @ X8) @ (k4_tarski @ X7 @ X9) @ 
% 0.38/0.57              (k4_tarski @ X10 @ X8) @ (k4_tarski @ X10 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t146_zfmisc_1])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.57         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 0.38/0.57           (k2_tarski @ X0 @ X3))
% 0.38/0.57           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 0.38/0.57              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3) @ 
% 0.38/0.57              (k4_tarski @ X4 @ X0) @ (k4_tarski @ X4 @ X3)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.57         ((k3_mcart_1 @ X15 @ X16 @ X17)
% 0.38/0.57           = (k4_tarski @ (k4_tarski @ X15 @ X16) @ X17))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.57         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X4) @ 
% 0.38/0.57           (k2_tarski @ X0 @ X3))
% 0.38/0.57           = (k2_enumset1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 0.38/0.57              (k3_mcart_1 @ X2 @ X1 @ X3) @ (k4_tarski @ X4 @ X0) @ 
% 0.38/0.57              (k4_tarski @ X4 @ X3)))),
% 0.38/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.57         ((k2_zfmisc_1 @ 
% 0.38/0.57           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 0.38/0.57           (k2_tarski @ X0 @ X3))
% 0.38/0.57           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 0.38/0.57              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 0.38/0.57              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['3', '8'])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.57         ((k3_mcart_1 @ X15 @ X16 @ X17)
% 0.38/0.57           = (k4_tarski @ (k4_tarski @ X15 @ X16) @ X17))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.57         ((k2_zfmisc_1 @ 
% 0.38/0.57           (k2_tarski @ (k4_tarski @ X5 @ X4) @ (k4_tarski @ X2 @ X1)) @ 
% 0.38/0.57           (k2_tarski @ X0 @ X3))
% 0.38/0.57           = (k2_enumset1 @ (k3_mcart_1 @ X5 @ X4 @ X0) @ 
% 0.38/0.57              (k3_mcart_1 @ X5 @ X4 @ X3) @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 0.38/0.57              (k3_mcart_1 @ X2 @ X1 @ X3)))),
% 0.38/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.57  thf(t36_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.38/0.57         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.38/0.57       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.38/0.57         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.38/0.57         ((k2_zfmisc_1 @ (k2_tarski @ X11 @ X12) @ (k1_tarski @ X14))
% 0.38/0.57           = (k2_tarski @ (k4_tarski @ X11 @ X14) @ (k4_tarski @ X12 @ X14)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.38/0.57  thf(d3_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.38/0.57       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.57         ((k3_zfmisc_1 @ X18 @ X19 @ X20)
% 0.38/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19) @ X20))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 0.38/0.57         (k2_tarski @ sk_D @ sk_E))
% 0.38/0.57         != (k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 0.38/0.57             (k2_tarski @ sk_D @ sk_E)))),
% 0.38/0.57      inference('demod', [status(thm)], ['2', '11', '12', '13'])).
% 0.38/0.57  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
