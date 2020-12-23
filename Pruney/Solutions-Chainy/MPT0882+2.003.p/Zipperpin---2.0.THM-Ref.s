%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xx7w8jBr8U

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:23 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   43 (  56 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  372 ( 527 expanded)
%              Number of equality atoms :   31 (  48 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t42_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_mcart_1 @ A @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) )
        = ( k2_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_mcart_1 @ A @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
 != ( k2_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ) )).

thf('1',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k4_mcart_1 @ X39 @ X40 @ X41 @ X42 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X39 @ X40 ) @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('2',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X43 @ X44 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('4',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k4_mcart_1 @ X35 @ X36 @ X37 @ X38 )
      = ( k4_tarski @ ( k3_mcart_1 @ X35 @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('5',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X43 @ X44 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ X3 @ X2 @ X1 )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('8',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X28 ) @ ( k2_tarski @ X29 @ X30 ) )
      = ( k2_tarski @ ( k4_tarski @ X28 @ X29 ) @ ( k4_tarski @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ X3 @ X2 @ X1 )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('13',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X28 ) @ ( k2_tarski @ X29 @ X30 ) )
      = ( k2_tarski @ ( k4_tarski @ X28 @ X29 ) @ ( k4_tarski @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('17',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k3_zfmisc_1 @ X32 @ X33 @ X34 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) @ X2 )
      = ( k2_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('20',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
 != ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xx7w8jBr8U
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.57  % Solved by: fo/fo7.sh
% 0.36/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.57  % done 114 iterations in 0.116s
% 0.36/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.57  % SZS output start Refutation
% 0.36/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.57  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.36/0.57  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.36/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.57  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.36/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.57  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.36/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.57  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.36/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.57  thf(t42_mcart_1, conjecture,
% 0.36/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.57     ( ( k3_zfmisc_1 @
% 0.36/0.57         ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) =
% 0.36/0.57       ( k2_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_mcart_1 @ A @ B @ D ) ) ))).
% 0.36/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.57        ( ( k3_zfmisc_1 @
% 0.36/0.57            ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) =
% 0.36/0.57          ( k2_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_mcart_1 @ A @ B @ D ) ) ) )),
% 0.36/0.57    inference('cnf.neg', [status(esa)], [t42_mcart_1])).
% 0.36/0.57  thf('0', plain,
% 0.36/0.57      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B) @ 
% 0.36/0.57         (k2_tarski @ sk_C @ sk_D))
% 0.36/0.57         != (k2_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.36/0.57             (k3_mcart_1 @ sk_A @ sk_B @ sk_D)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t31_mcart_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.57     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.36/0.57       ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ))).
% 0.36/0.57  thf('1', plain,
% 0.36/0.57      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.36/0.57         ((k4_mcart_1 @ X39 @ X40 @ X41 @ X42)
% 0.36/0.57           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X39 @ X40) @ X41) @ X42))),
% 0.36/0.57      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.36/0.57  thf(t7_mcart_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.36/0.57       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.36/0.57  thf('2', plain,
% 0.36/0.57      (![X43 : $i, X44 : $i]: ((k1_mcart_1 @ (k4_tarski @ X43 @ X44)) = (X43))),
% 0.36/0.57      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.36/0.57  thf('3', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.57         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.36/0.57           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.36/0.57      inference('sup+', [status(thm)], ['1', '2'])).
% 0.36/0.57  thf(d4_mcart_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.57     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.36/0.57       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.36/0.57  thf('4', plain,
% 0.36/0.57      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.36/0.57         ((k4_mcart_1 @ X35 @ X36 @ X37 @ X38)
% 0.36/0.57           = (k4_tarski @ (k3_mcart_1 @ X35 @ X36 @ X37) @ X38))),
% 0.36/0.57      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.36/0.57  thf('5', plain,
% 0.36/0.57      (![X43 : $i, X44 : $i]: ((k1_mcart_1 @ (k4_tarski @ X43 @ X44)) = (X43))),
% 0.36/0.57      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.36/0.57  thf('6', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.57         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.36/0.57           = (k3_mcart_1 @ X3 @ X2 @ X1))),
% 0.36/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.36/0.57  thf('7', plain,
% 0.36/0.57      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.57         ((k3_mcart_1 @ X3 @ X2 @ X1)
% 0.36/0.57           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.36/0.57      inference('demod', [status(thm)], ['3', '6'])).
% 0.36/0.57  thf(t36_zfmisc_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.36/0.57         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.36/0.57       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.36/0.57         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.36/0.57  thf('8', plain,
% 0.36/0.57      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.57         ((k2_zfmisc_1 @ (k1_tarski @ X28) @ (k2_tarski @ X29 @ X30))
% 0.36/0.57           = (k2_tarski @ (k4_tarski @ X28 @ X29) @ (k4_tarski @ X28 @ X30)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.36/0.57  thf('9', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.57         ((k2_zfmisc_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)) @ 
% 0.36/0.57           (k2_tarski @ X0 @ X3))
% 0.36/0.57           = (k2_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 0.36/0.57              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3)))),
% 0.36/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.36/0.57  thf('10', plain,
% 0.36/0.57      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.57         ((k3_mcart_1 @ X3 @ X2 @ X1)
% 0.36/0.57           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.36/0.57      inference('demod', [status(thm)], ['3', '6'])).
% 0.36/0.57  thf('11', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.57         ((k2_zfmisc_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)) @ 
% 0.36/0.57           (k2_tarski @ X0 @ X3))
% 0.36/0.57           = (k2_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 0.36/0.57              (k3_mcart_1 @ X2 @ X1 @ X3)))),
% 0.36/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.57  thf(t69_enumset1, axiom,
% 0.36/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.57  thf('12', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.36/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.57  thf('13', plain,
% 0.36/0.57      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.57         ((k2_zfmisc_1 @ (k1_tarski @ X28) @ (k2_tarski @ X29 @ X30))
% 0.36/0.57           = (k2_tarski @ (k4_tarski @ X28 @ X29) @ (k4_tarski @ X28 @ X30)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.36/0.57  thf('14', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 0.36/0.57           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.36/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.36/0.57  thf('15', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.36/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.57  thf('16', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.36/0.57           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.36/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.36/0.57  thf(d3_zfmisc_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.36/0.57       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.36/0.57  thf('17', plain,
% 0.36/0.57      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.36/0.57         ((k3_zfmisc_1 @ X32 @ X33 @ X34)
% 0.36/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33) @ X34))),
% 0.36/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.57  thf('18', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.57         ((k3_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0) @ X2)
% 0.36/0.57           = (k2_zfmisc_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)) @ X2))),
% 0.36/0.57      inference('sup+', [status(thm)], ['16', '17'])).
% 0.36/0.57  thf('19', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.57         ((k3_zfmisc_1 @ (k1_tarski @ X2) @ (k1_tarski @ X1) @ 
% 0.36/0.57           (k2_tarski @ X0 @ X3))
% 0.36/0.57           = (k2_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 0.36/0.57              (k3_mcart_1 @ X2 @ X1 @ X3)))),
% 0.36/0.57      inference('demod', [status(thm)], ['11', '18'])).
% 0.36/0.57  thf('20', plain,
% 0.36/0.57      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B) @ 
% 0.36/0.57         (k2_tarski @ sk_C @ sk_D))
% 0.36/0.57         != (k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B) @ 
% 0.36/0.57             (k2_tarski @ sk_C @ sk_D)))),
% 0.36/0.57      inference('demod', [status(thm)], ['0', '19'])).
% 0.36/0.57  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.36/0.57  
% 0.36/0.57  % SZS output end Refutation
% 0.36/0.57  
% 0.36/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
