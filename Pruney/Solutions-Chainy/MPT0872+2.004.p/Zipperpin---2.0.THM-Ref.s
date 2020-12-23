%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PgVELimEDj

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  199 ( 235 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf('#_fresh_sk1_type',type,(
    '#_fresh_sk1': $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t32_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k3_mcart_1 @ ( k4_tarski @ A @ B ) @ C @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k4_mcart_1 @ A @ B @ C @ D )
        = ( k3_mcart_1 @ ( k4_tarski @ A @ B ) @ C @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t32_mcart_1])).

thf('0',plain,(
    ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k3_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k4_mcart_1 @ X8 @ X9 @ X10 @ X11 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X8 @ X9 ) @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k4_mcart_1 @ X8 @ X9 @ X10 @ X11 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X8 @ X9 ) @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_mcart_1 @ ( k4_tarski @ X3 @ X2 ) @ X1 @ X0 @ X4 )
      = ( k4_tarski @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k4_mcart_1 @ X4 @ X5 @ X6 @ X7 )
      = ( k4_tarski @ ( k3_mcart_1 @ X4 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf(t33_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k4_tarski @ A @ B )
        = ( k4_tarski @ C @ D ) )
     => ( ( A = C )
        & ( B = D ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( ( k4_tarski @ X1 @ X3 )
       != ( k4_tarski @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X3 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ ( k4_mcart_1 @ X4 @ X3 @ X2 @ X1 ) @ X0 ) )
      = ( k3_mcart_1 @ ( k4_tarski @ X4 @ X3 ) @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X3 ) )
      = X1 ) ),
    inference(inj_rec,[status(thm)],['5'])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_mcart_1 @ X4 @ X3 @ X2 @ X1 )
      = ( k3_mcart_1 @ ( k4_tarski @ X4 @ X3 ) @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','10'])).

thf('12',plain,(
    $false ),
    inference(simplify,[status(thm)],['11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PgVELimEDj
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:33:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 26 iterations in 0.012s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.46  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.46  thf('#_fresh_sk1_type', type, '#_fresh_sk1': $i > $i).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(t32_mcart_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.46       ( k3_mcart_1 @ ( k4_tarski @ A @ B ) @ C @ D ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46        ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.46          ( k3_mcart_1 @ ( k4_tarski @ A @ B ) @ C @ D ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t32_mcart_1])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.46         != (k3_mcart_1 @ (k4_tarski @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t31_mcart_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.46       ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.46         ((k4_mcart_1 @ X8 @ X9 @ X10 @ X11)
% 0.21/0.46           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X8 @ X9) @ X10) @ X11))),
% 0.21/0.46      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.46         ((k4_mcart_1 @ X8 @ X9 @ X10 @ X11)
% 0.21/0.46           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X8 @ X9) @ X10) @ X11))),
% 0.21/0.46      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.46         ((k4_mcart_1 @ (k4_tarski @ X3 @ X2) @ X1 @ X0 @ X4)
% 0.21/0.46           = (k4_tarski @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 0.21/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf(d4_mcart_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.46       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.46         ((k4_mcart_1 @ X4 @ X5 @ X6 @ X7)
% 0.21/0.46           = (k4_tarski @ (k3_mcart_1 @ X4 @ X5 @ X6) @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.21/0.46  thf(t33_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( ( k4_tarski @ A @ B ) = ( k4_tarski @ C @ D ) ) =>
% 0.21/0.46       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.46         (((X1) = (X0)) | ((k4_tarski @ X1 @ X3) != (k4_tarski @ X0 @ X2)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t33_zfmisc_1])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X1 : $i, X3 : $i]: (('#_fresh_sk1' @ (k4_tarski @ X1 @ X3)) = (X1))),
% 0.21/0.46      inference('inj_rec', [status(thm)], ['5'])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.46         (('#_fresh_sk1' @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.46           = (k3_mcart_1 @ X3 @ X2 @ X1))),
% 0.21/0.46      inference('sup+', [status(thm)], ['4', '6'])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.46         (('#_fresh_sk1' @ (k4_tarski @ (k4_mcart_1 @ X4 @ X3 @ X2 @ X1) @ X0))
% 0.21/0.46           = (k3_mcart_1 @ (k4_tarski @ X4 @ X3) @ X2 @ X1))),
% 0.21/0.46      inference('sup+', [status(thm)], ['3', '7'])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X1 : $i, X3 : $i]: (('#_fresh_sk1' @ (k4_tarski @ X1 @ X3)) = (X1))),
% 0.21/0.46      inference('inj_rec', [status(thm)], ['5'])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.46         ((k4_mcart_1 @ X4 @ X3 @ X2 @ X1)
% 0.21/0.46           = (k3_mcart_1 @ (k4_tarski @ X4 @ X3) @ X2 @ X1))),
% 0.21/0.46      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.46         != (k4_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.46      inference('demod', [status(thm)], ['0', '10'])).
% 0.21/0.46  thf('12', plain, ($false), inference('simplify', [status(thm)], ['11'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
