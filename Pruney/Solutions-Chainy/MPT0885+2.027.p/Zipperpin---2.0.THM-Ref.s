%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2aSdnwf1Pu

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:31 EST 2020

% Result     : Theorem 25.00s
% Output     : Refutation 25.00s
% Verified   : 
% Statistics : Number of formulae       :   41 (  57 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :  482 ( 715 expanded)
%              Number of equality atoms :   29 (  48 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

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

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t45_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) )
      = ( k2_enumset1 @ ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) )
        = ( k2_enumset1 @ ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k2_enumset1 @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_E ) @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X9 ) @ ( k2_tarski @ X10 @ X11 ) )
      = ( k2_tarski @ ( k4_tarski @ X9 @ X10 ) @ ( k4_tarski @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('2',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X9 @ X10 ) @ ( k1_tarski @ X12 ) )
      = ( k2_tarski @ ( k4_tarski @ X9 @ X12 ) @ ( k4_tarski @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_tarski @ X3 ) )
      = ( k2_tarski @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_zfmisc_1 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_mcart_1 @ X13 @ X14 @ X15 )
      = ( k4_tarski @ ( k4_tarski @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_mcart_1 @ X13 @ X14 @ X15 )
      = ( k4_tarski @ ( k4_tarski @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) @ ( k3_mcart_1 @ X2 @ X0 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_zfmisc_1 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t132_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ ( k2_tarski @ X5 @ X7 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X8 @ ( k1_tarski @ X5 ) ) @ ( k2_zfmisc_1 @ X8 @ ( k1_tarski @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[t132_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ ( k1_tarski @ X0 ) ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k1_tarski @ X3 ) ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_zfmisc_1 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('12',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_zfmisc_1 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ X2 @ X1 @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ ( k1_tarski @ X0 ) ) @ ( k3_zfmisc_1 @ X2 @ X1 @ ( k1_tarski @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X3 @ X1 ) @ ( k2_tarski @ X0 @ X4 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ ( k3_mcart_1 @ X2 @ X3 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) @ ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X3 @ X1 ) @ ( k1_tarski @ X4 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) @ ( k3_mcart_1 @ X2 @ X0 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X5 @ X4 @ ( k3_mcart_1 @ X3 @ X2 @ X0 ) @ ( k3_mcart_1 @ X3 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k3_zfmisc_1 @ ( k1_tarski @ X3 ) @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_enumset1 @ ( k3_mcart_1 @ X4 @ X3 @ X1 ) @ ( k3_mcart_1 @ X4 @ X2 @ X1 ) @ ( k3_mcart_1 @ X4 @ X3 @ X0 ) @ ( k3_mcart_1 @ X4 @ X2 @ X0 ) )
      = ( k3_zfmisc_1 @ ( k1_tarski @ X4 ) @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) )
 != ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['0','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2aSdnwf1Pu
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:59:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 25.00/25.23  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 25.00/25.23  % Solved by: fo/fo7.sh
% 25.00/25.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 25.00/25.23  % done 4949 iterations in 24.773s
% 25.00/25.23  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 25.00/25.23  % SZS output start Refutation
% 25.00/25.23  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 25.00/25.23  thf(sk_E_type, type, sk_E: $i).
% 25.00/25.23  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 25.00/25.23  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 25.00/25.23  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 25.00/25.23  thf(sk_D_type, type, sk_D: $i).
% 25.00/25.23  thf(sk_C_type, type, sk_C: $i).
% 25.00/25.23  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 25.00/25.23  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 25.00/25.23  thf(sk_A_type, type, sk_A: $i).
% 25.00/25.23  thf(sk_B_type, type, sk_B: $i).
% 25.00/25.23  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 25.00/25.23  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 25.00/25.23  thf(t45_mcart_1, conjecture,
% 25.00/25.23    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 25.00/25.23     ( ( k3_zfmisc_1 @
% 25.00/25.23         ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) =
% 25.00/25.23       ( k2_enumset1 @
% 25.00/25.23         ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ 
% 25.00/25.23         ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ))).
% 25.00/25.23  thf(zf_stmt_0, negated_conjecture,
% 25.00/25.23    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 25.00/25.23        ( ( k3_zfmisc_1 @
% 25.00/25.23            ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) =
% 25.00/25.23          ( k2_enumset1 @
% 25.00/25.23            ( k3_mcart_1 @ A @ B @ D ) @ ( k3_mcart_1 @ A @ C @ D ) @ 
% 25.00/25.23            ( k3_mcart_1 @ A @ B @ E ) @ ( k3_mcart_1 @ A @ C @ E ) ) ) )),
% 25.00/25.23    inference('cnf.neg', [status(esa)], [t45_mcart_1])).
% 25.00/25.23  thf('0', plain,
% 25.00/25.23      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 25.00/25.23         (k2_tarski @ sk_D @ sk_E))
% 25.00/25.23         != (k2_enumset1 @ (k3_mcart_1 @ sk_A @ sk_B @ sk_D) @ 
% 25.00/25.23             (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 25.00/25.23             (k3_mcart_1 @ sk_A @ sk_B @ sk_E) @ 
% 25.00/25.23             (k3_mcart_1 @ sk_A @ sk_C @ sk_E)))),
% 25.00/25.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.00/25.23  thf(t36_zfmisc_1, axiom,
% 25.00/25.23    (![A:$i,B:$i,C:$i]:
% 25.00/25.23     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 25.00/25.23         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 25.00/25.23       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 25.00/25.23         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 25.00/25.23  thf('1', plain,
% 25.00/25.23      (![X9 : $i, X10 : $i, X11 : $i]:
% 25.00/25.23         ((k2_zfmisc_1 @ (k1_tarski @ X9) @ (k2_tarski @ X10 @ X11))
% 25.00/25.23           = (k2_tarski @ (k4_tarski @ X9 @ X10) @ (k4_tarski @ X9 @ X11)))),
% 25.00/25.23      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 25.00/25.23  thf('2', plain,
% 25.00/25.23      (![X9 : $i, X10 : $i, X12 : $i]:
% 25.00/25.23         ((k2_zfmisc_1 @ (k2_tarski @ X9 @ X10) @ (k1_tarski @ X12))
% 25.00/25.23           = (k2_tarski @ (k4_tarski @ X9 @ X12) @ (k4_tarski @ X10 @ X12)))),
% 25.00/25.23      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 25.00/25.23  thf('3', plain,
% 25.00/25.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.00/25.23         ((k2_zfmisc_1 @ 
% 25.00/25.23           (k2_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)) @ 
% 25.00/25.23           (k1_tarski @ X3))
% 25.00/25.23           = (k2_tarski @ (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3) @ 
% 25.00/25.23              (k4_tarski @ (k4_tarski @ X2 @ X0) @ X3)))),
% 25.00/25.23      inference('sup+', [status(thm)], ['1', '2'])).
% 25.00/25.23  thf(d3_zfmisc_1, axiom,
% 25.00/25.23    (![A:$i,B:$i,C:$i]:
% 25.00/25.23     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 25.00/25.23       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 25.00/25.23  thf('4', plain,
% 25.00/25.23      (![X16 : $i, X17 : $i, X18 : $i]:
% 25.00/25.23         ((k3_zfmisc_1 @ X16 @ X17 @ X18)
% 25.00/25.23           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17) @ X18))),
% 25.00/25.23      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 25.00/25.23  thf(d3_mcart_1, axiom,
% 25.00/25.23    (![A:$i,B:$i,C:$i]:
% 25.00/25.23     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 25.00/25.23  thf('5', plain,
% 25.00/25.23      (![X13 : $i, X14 : $i, X15 : $i]:
% 25.00/25.23         ((k3_mcart_1 @ X13 @ X14 @ X15)
% 25.00/25.23           = (k4_tarski @ (k4_tarski @ X13 @ X14) @ X15))),
% 25.00/25.23      inference('cnf', [status(esa)], [d3_mcart_1])).
% 25.00/25.23  thf('6', plain,
% 25.00/25.23      (![X13 : $i, X14 : $i, X15 : $i]:
% 25.00/25.23         ((k3_mcart_1 @ X13 @ X14 @ X15)
% 25.00/25.23           = (k4_tarski @ (k4_tarski @ X13 @ X14) @ X15))),
% 25.00/25.23      inference('cnf', [status(esa)], [d3_mcart_1])).
% 25.00/25.23  thf('7', plain,
% 25.00/25.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.00/25.23         ((k3_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0) @ 
% 25.00/25.23           (k1_tarski @ X3))
% 25.00/25.23           = (k2_tarski @ (k3_mcart_1 @ X2 @ X1 @ X3) @ 
% 25.00/25.23              (k3_mcart_1 @ X2 @ X0 @ X3)))),
% 25.00/25.23      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 25.00/25.23  thf('8', plain,
% 25.00/25.23      (![X16 : $i, X17 : $i, X18 : $i]:
% 25.00/25.23         ((k3_zfmisc_1 @ X16 @ X17 @ X18)
% 25.00/25.23           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17) @ X18))),
% 25.00/25.23      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 25.00/25.23  thf(t132_zfmisc_1, axiom,
% 25.00/25.23    (![A:$i,B:$i,C:$i]:
% 25.00/25.23     ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 25.00/25.23         ( k2_xboole_0 @
% 25.00/25.23           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 25.00/25.23           ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) ) & 
% 25.00/25.23       ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C ) =
% 25.00/25.23         ( k2_xboole_0 @
% 25.00/25.23           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 25.00/25.23           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ))).
% 25.00/25.23  thf('9', plain,
% 25.00/25.23      (![X5 : $i, X7 : $i, X8 : $i]:
% 25.00/25.23         ((k2_zfmisc_1 @ X8 @ (k2_tarski @ X5 @ X7))
% 25.00/25.23           = (k2_xboole_0 @ (k2_zfmisc_1 @ X8 @ (k1_tarski @ X5)) @ 
% 25.00/25.23              (k2_zfmisc_1 @ X8 @ (k1_tarski @ X7))))),
% 25.00/25.23      inference('cnf', [status(esa)], [t132_zfmisc_1])).
% 25.00/25.23  thf('10', plain,
% 25.00/25.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.00/25.23         ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ (k2_tarski @ X0 @ X3))
% 25.00/25.23           = (k2_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ (k1_tarski @ X0)) @ 
% 25.00/25.23              (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ (k1_tarski @ X3))))),
% 25.00/25.23      inference('sup+', [status(thm)], ['8', '9'])).
% 25.00/25.23  thf('11', plain,
% 25.00/25.23      (![X16 : $i, X17 : $i, X18 : $i]:
% 25.00/25.23         ((k3_zfmisc_1 @ X16 @ X17 @ X18)
% 25.00/25.23           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17) @ X18))),
% 25.00/25.23      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 25.00/25.23  thf('12', plain,
% 25.00/25.23      (![X16 : $i, X17 : $i, X18 : $i]:
% 25.00/25.23         ((k3_zfmisc_1 @ X16 @ X17 @ X18)
% 25.00/25.23           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17) @ X18))),
% 25.00/25.23      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 25.00/25.23  thf('13', plain,
% 25.00/25.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.00/25.23         ((k3_zfmisc_1 @ X2 @ X1 @ (k2_tarski @ X0 @ X3))
% 25.00/25.23           = (k2_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ (k1_tarski @ X0)) @ 
% 25.00/25.23              (k3_zfmisc_1 @ X2 @ X1 @ (k1_tarski @ X3))))),
% 25.00/25.23      inference('demod', [status(thm)], ['10', '11', '12'])).
% 25.00/25.23  thf('14', plain,
% 25.00/25.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 25.00/25.23         ((k3_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X3 @ X1) @ 
% 25.00/25.23           (k2_tarski @ X0 @ X4))
% 25.00/25.23           = (k2_xboole_0 @ 
% 25.00/25.23              (k2_tarski @ (k3_mcart_1 @ X2 @ X3 @ X0) @ 
% 25.00/25.23               (k3_mcart_1 @ X2 @ X1 @ X0)) @ 
% 25.00/25.23              (k3_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X3 @ X1) @ 
% 25.00/25.23               (k1_tarski @ X4))))),
% 25.00/25.23      inference('sup+', [status(thm)], ['7', '13'])).
% 25.00/25.23  thf('15', plain,
% 25.00/25.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.00/25.23         ((k3_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0) @ 
% 25.00/25.23           (k1_tarski @ X3))
% 25.00/25.23           = (k2_tarski @ (k3_mcart_1 @ X2 @ X1 @ X3) @ 
% 25.00/25.23              (k3_mcart_1 @ X2 @ X0 @ X3)))),
% 25.00/25.23      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 25.00/25.23  thf(l53_enumset1, axiom,
% 25.00/25.23    (![A:$i,B:$i,C:$i,D:$i]:
% 25.00/25.23     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 25.00/25.23       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 25.00/25.23  thf('16', plain,
% 25.00/25.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.00/25.23         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 25.00/25.23           = (k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X2 @ X3)))),
% 25.00/25.23      inference('cnf', [status(esa)], [l53_enumset1])).
% 25.00/25.23  thf('17', plain,
% 25.00/25.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 25.00/25.23         ((k2_enumset1 @ X5 @ X4 @ (k3_mcart_1 @ X3 @ X2 @ X0) @ 
% 25.00/25.23           (k3_mcart_1 @ X3 @ X1 @ X0))
% 25.00/25.23           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 25.00/25.23              (k3_zfmisc_1 @ (k1_tarski @ X3) @ (k2_tarski @ X2 @ X1) @ 
% 25.00/25.23               (k1_tarski @ X0))))),
% 25.00/25.23      inference('sup+', [status(thm)], ['15', '16'])).
% 25.00/25.23  thf('18', plain,
% 25.00/25.23      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 25.00/25.23         ((k2_enumset1 @ (k3_mcart_1 @ X4 @ X3 @ X1) @ 
% 25.00/25.23           (k3_mcart_1 @ X4 @ X2 @ X1) @ (k3_mcart_1 @ X4 @ X3 @ X0) @ 
% 25.00/25.23           (k3_mcart_1 @ X4 @ X2 @ X0))
% 25.00/25.23           = (k3_zfmisc_1 @ (k1_tarski @ X4) @ (k2_tarski @ X3 @ X2) @ 
% 25.00/25.23              (k2_tarski @ X1 @ X0)))),
% 25.00/25.23      inference('sup+', [status(thm)], ['14', '17'])).
% 25.00/25.23  thf('19', plain,
% 25.00/25.23      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 25.00/25.23         (k2_tarski @ sk_D @ sk_E))
% 25.00/25.23         != (k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C) @ 
% 25.00/25.23             (k2_tarski @ sk_D @ sk_E)))),
% 25.00/25.23      inference('demod', [status(thm)], ['0', '18'])).
% 25.00/25.23  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 25.00/25.23  
% 25.00/25.23  % SZS output end Refutation
% 25.00/25.23  
% 25.08/25.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
