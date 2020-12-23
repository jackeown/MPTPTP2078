%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CrrqLsarjw

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :  329 ( 369 expanded)
%              Number of equality atoms :   27 (  31 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t65_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) )
      = ( k1_tarski @ ( k4_mcart_1 @ A @ B @ C @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k4_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) )
        = ( k1_tarski @ ( k4_mcart_1 @ A @ B @ C @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_mcart_1])).

thf('0',plain,(
    ( k4_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) )
 != ( k1_tarski @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t53_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) @ X18 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) @ X3 @ X2 )
      = ( k4_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) @ X3 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf(t39_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) )
      = ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) @ ( k1_tarski @ X14 ) )
      = ( k1_tarski @ ( k3_mcart_1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t39_mcart_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_mcart_1 @ X2 @ X3 @ X4 )
      = ( k4_tarski @ ( k4_tarski @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_mcart_1 @ X2 @ X3 @ X4 )
      = ( k4_tarski @ ( k4_tarski @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t31_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k4_mcart_1 @ X8 @ X9 @ X10 @ X11 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X8 @ X9 ) @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_mcart_1 @ X2 @ X3 @ X4 )
      = ( k4_tarski @ ( k4_tarski @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k4_mcart_1 @ X8 @ X9 @ X10 @ X11 )
      = ( k4_tarski @ ( k3_mcart_1 @ X8 @ X9 @ X10 ) @ X11 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_mcart_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ( k1_tarski @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
 != ( k1_tarski @ ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','9','10','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CrrqLsarjw
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:41:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 14 iterations in 0.013s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.46  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.46  thf(t65_mcart_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( k4_zfmisc_1 @
% 0.20/0.46         ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) @ 
% 0.20/0.46         ( k1_tarski @ D ) ) =
% 0.20/0.46       ( k1_tarski @ ( k4_mcart_1 @ A @ B @ C @ D ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46        ( ( k4_zfmisc_1 @
% 0.20/0.46            ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) @ 
% 0.20/0.46            ( k1_tarski @ D ) ) =
% 0.20/0.46          ( k1_tarski @ ( k4_mcart_1 @ A @ B @ C @ D ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t65_mcart_1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (((k4_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B) @ 
% 0.20/0.46         (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))
% 0.20/0.46         != (k1_tarski @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t35_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.46       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.20/0.46           = (k1_tarski @ (k4_tarski @ X0 @ X1)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.20/0.46  thf(d3_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.46       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.46         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.20/0.46           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.46         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.20/0.46           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.20/0.46           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.20/0.46      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf(t53_mcart_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.20/0.46       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.46         ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18)
% 0.20/0.46           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17) @ 
% 0.20/0.46              X18))),
% 0.20/0.46      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.46         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.20/0.46           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.46         ((k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18)
% 0.20/0.46           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X15 @ X16 @ X17) @ X18))),
% 0.20/0.46      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.20/0.46           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.20/0.46      inference('demod', [status(thm)], ['4', '7'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((k3_zfmisc_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)) @ X3 @ X2)
% 0.20/0.46           = (k4_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0) @ X3 @ X2))),
% 0.20/0.46      inference('sup+', [status(thm)], ['1', '8'])).
% 0.20/0.46  thf(t39_mcart_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( k3_zfmisc_1 @
% 0.20/0.46         ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) =
% 0.20/0.46       ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ))).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.46         ((k3_zfmisc_1 @ (k1_tarski @ X12) @ (k1_tarski @ X13) @ 
% 0.20/0.46           (k1_tarski @ X14)) = (k1_tarski @ (k3_mcart_1 @ X12 @ X13 @ X14)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t39_mcart_1])).
% 0.20/0.46  thf(d3_mcart_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.46         ((k3_mcart_1 @ X2 @ X3 @ X4)
% 0.20/0.46           = (k4_tarski @ (k4_tarski @ X2 @ X3) @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.46         ((k3_mcart_1 @ X2 @ X3 @ X4)
% 0.20/0.46           = (k4_tarski @ (k4_tarski @ X2 @ X3) @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.20/0.46           = (k4_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X3))),
% 0.20/0.46      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.46  thf(t31_mcart_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.46       ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ))).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.46         ((k4_mcart_1 @ X8 @ X9 @ X10 @ X11)
% 0.20/0.46           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X8 @ X9) @ X10) @ X11))),
% 0.20/0.46      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.46         ((k3_mcart_1 @ X2 @ X3 @ X4)
% 0.20/0.46           = (k4_tarski @ (k4_tarski @ X2 @ X3) @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.46         ((k4_mcart_1 @ X8 @ X9 @ X10 @ X11)
% 0.20/0.46           = (k4_tarski @ (k3_mcart_1 @ X8 @ X9 @ X10) @ X11))),
% 0.20/0.46      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 0.20/0.46           = (k4_mcart_1 @ X2 @ X1 @ X0 @ X3))),
% 0.20/0.46      inference('demod', [status(thm)], ['13', '16'])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (((k1_tarski @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.20/0.46         != (k1_tarski @ (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '9', '10', '17'])).
% 0.20/0.46  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
