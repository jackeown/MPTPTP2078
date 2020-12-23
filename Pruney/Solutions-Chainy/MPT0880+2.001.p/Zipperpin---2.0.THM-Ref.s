%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gimo3ObImC

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:22 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   25 (  27 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :  217 ( 255 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t40_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) )
      = ( k2_tarski @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k3_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) )
        = ( k2_tarski @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) )
 != ( k2_tarski @ ( k3_mcart_1 @ sk_A @ sk_C @ sk_D ) @ ( k3_mcart_1 @ sk_B @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X3 ) @ ( k1_tarski @ X5 ) )
      = ( k2_tarski @ ( k4_tarski @ X2 @ X5 ) @ ( k4_tarski @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('2',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X3 ) @ ( k1_tarski @ X5 ) )
      = ( k2_tarski @ ( k4_tarski @ X2 @ X5 ) @ ( k4_tarski @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X3 ) )
      = ( k2_tarski @ ( k4_tarski @ ( k4_tarski @ X2 @ X0 ) @ X3 ) @ ( k4_tarski @ ( k4_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_mcart_1 @ X6 @ X7 @ X8 )
      = ( k4_tarski @ ( k4_tarski @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_mcart_1 @ X6 @ X7 @ X8 )
      = ( k4_tarski @ ( k4_tarski @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X0 @ X3 ) @ ( k3_mcart_1 @ X1 @ X0 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) )
 != ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gimo3ObImC
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 62 iterations in 0.096s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.55  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.55  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.55  thf(t40_mcart_1, conjecture,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( k3_zfmisc_1 @
% 0.36/0.55         ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) =
% 0.36/0.55       ( k2_tarski @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55        ( ( k3_zfmisc_1 @
% 0.36/0.55            ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) =
% 0.36/0.55          ( k2_tarski @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t40_mcart_1])).
% 0.36/0.55  thf('0', plain,
% 0.36/0.55      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 0.36/0.55         (k1_tarski @ sk_D))
% 0.36/0.55         != (k2_tarski @ (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.36/0.55             (k3_mcart_1 @ sk_B @ sk_C @ sk_D)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t36_zfmisc_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.36/0.55         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.36/0.55       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.36/0.55         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.36/0.55         ((k2_zfmisc_1 @ (k2_tarski @ X2 @ X3) @ (k1_tarski @ X5))
% 0.36/0.55           = (k2_tarski @ (k4_tarski @ X2 @ X5) @ (k4_tarski @ X3 @ X5)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.36/0.55         ((k2_zfmisc_1 @ (k2_tarski @ X2 @ X3) @ (k1_tarski @ X5))
% 0.36/0.55           = (k2_tarski @ (k4_tarski @ X2 @ X5) @ (k4_tarski @ X3 @ X5)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.55         ((k2_zfmisc_1 @ 
% 0.36/0.55           (k2_zfmisc_1 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)) @ 
% 0.36/0.55           (k1_tarski @ X3))
% 0.36/0.55           = (k2_tarski @ (k4_tarski @ (k4_tarski @ X2 @ X0) @ X3) @ 
% 0.36/0.55              (k4_tarski @ (k4_tarski @ X1 @ X0) @ X3)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['1', '2'])).
% 0.36/0.55  thf(d3_zfmisc_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.36/0.55       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.55         ((k3_zfmisc_1 @ X9 @ X10 @ X11)
% 0.36/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10) @ X11))),
% 0.36/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.55  thf(d3_mcart_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.55         ((k3_mcart_1 @ X6 @ X7 @ X8)
% 0.36/0.55           = (k4_tarski @ (k4_tarski @ X6 @ X7) @ X8))),
% 0.36/0.55      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.55         ((k3_mcart_1 @ X6 @ X7 @ X8)
% 0.36/0.55           = (k4_tarski @ (k4_tarski @ X6 @ X7) @ X8))),
% 0.36/0.55      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.55         ((k3_zfmisc_1 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0) @ 
% 0.36/0.55           (k1_tarski @ X3))
% 0.36/0.55           = (k2_tarski @ (k3_mcart_1 @ X2 @ X0 @ X3) @ 
% 0.36/0.55              (k3_mcart_1 @ X1 @ X0 @ X3)))),
% 0.36/0.55      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 0.36/0.55         (k1_tarski @ sk_D))
% 0.36/0.55         != (k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 0.36/0.55             (k1_tarski @ sk_D)))),
% 0.36/0.55      inference('demod', [status(thm)], ['0', '7'])).
% 0.36/0.55  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
