%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2uMzOUp9fU

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :  233 ( 271 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

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
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X1 @ X2 ) @ ( k1_tarski @ X4 ) )
      = ( k2_tarski @ ( k4_tarski @ X1 @ X4 ) @ ( k4_tarski @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_mcart_1 @ X5 @ X6 @ X7 )
      = ( k4_tarski @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X1 @ X2 ) @ ( k1_tarski @ X4 ) )
      = ( k2_tarski @ ( k4_tarski @ X1 @ X4 ) @ ( k4_tarski @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ X3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X3 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X0 @ X3 ) @ ( k4_tarski @ ( k4_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_mcart_1 @ X5 @ X6 @ X7 )
      = ( k4_tarski @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X0 @ X3 ) @ ( k3_mcart_1 @ X1 @ X0 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) )
 != ( k3_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','8'])).

thf('10',plain,(
    $false ),
    inference(simplify,[status(thm)],['9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2uMzOUp9fU
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 25 iterations in 0.026s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.46  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.46  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.46  thf(t40_mcart_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( k3_zfmisc_1 @
% 0.20/0.46         ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) =
% 0.20/0.46       ( k2_tarski @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46        ( ( k3_zfmisc_1 @
% 0.20/0.46            ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) =
% 0.20/0.46          ( k2_tarski @ ( k3_mcart_1 @ A @ C @ D ) @ ( k3_mcart_1 @ B @ C @ D ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t40_mcart_1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 0.20/0.46         (k1_tarski @ sk_D))
% 0.20/0.46         != (k2_tarski @ (k3_mcart_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.20/0.46             (k3_mcart_1 @ sk_B @ sk_C @ sk_D)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t36_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.20/0.46         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.20/0.46       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.20/0.46         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.46         ((k2_zfmisc_1 @ (k2_tarski @ X1 @ X2) @ (k1_tarski @ X4))
% 0.20/0.46           = (k2_tarski @ (k4_tarski @ X1 @ X4) @ (k4_tarski @ X2 @ X4)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.20/0.46  thf(d3_mcart_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.46         ((k3_mcart_1 @ X5 @ X6 @ X7)
% 0.20/0.46           = (k4_tarski @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.46         ((k2_zfmisc_1 @ (k2_tarski @ X1 @ X2) @ (k1_tarski @ X4))
% 0.20/0.46           = (k2_tarski @ (k4_tarski @ X1 @ X4) @ (k4_tarski @ X2 @ X4)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((k2_zfmisc_1 @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X3) @ 
% 0.20/0.46           (k1_tarski @ X0))
% 0.20/0.46           = (k2_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ (k4_tarski @ X3 @ X0)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((k2_zfmisc_1 @ 
% 0.20/0.46           (k2_zfmisc_1 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)) @ 
% 0.20/0.46           (k1_tarski @ X3))
% 0.20/0.46           = (k2_tarski @ (k3_mcart_1 @ X2 @ X0 @ X3) @ 
% 0.20/0.46              (k4_tarski @ (k4_tarski @ X1 @ X0) @ X3)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['1', '4'])).
% 0.20/0.46  thf(d3_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.46       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.46         ((k3_zfmisc_1 @ X8 @ X9 @ X10)
% 0.20/0.46           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9) @ X10))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.46         ((k3_mcart_1 @ X5 @ X6 @ X7)
% 0.20/0.46           = (k4_tarski @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         ((k3_zfmisc_1 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0) @ 
% 0.20/0.46           (k1_tarski @ X3))
% 0.20/0.46           = (k2_tarski @ (k3_mcart_1 @ X2 @ X0 @ X3) @ 
% 0.20/0.46              (k3_mcart_1 @ X1 @ X0 @ X3)))),
% 0.20/0.46      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (((k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 0.20/0.46         (k1_tarski @ sk_D))
% 0.20/0.46         != (k3_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C) @ 
% 0.20/0.46             (k1_tarski @ sk_D)))),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '8'])).
% 0.20/0.46  thf('10', plain, ($false), inference('simplify', [status(thm)], ['9'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
