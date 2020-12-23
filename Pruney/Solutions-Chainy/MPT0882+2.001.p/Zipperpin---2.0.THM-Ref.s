%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DBjZUDUHrD

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  29 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :  252 ( 262 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_mcart_1 @ X8 @ X9 @ X10 )
      = ( k4_tarski @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X4 ) @ ( k2_tarski @ X5 @ X6 ) )
      = ( k2_tarski @ ( k4_tarski @ X4 @ X5 ) @ ( k4_tarski @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_mcart_1 @ X8 @ X9 @ X10 )
      = ( k4_tarski @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X3 ) )
      = ( k1_tarski @ ( k4_tarski @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) @ X2 )
      = ( k2_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X3 ) )
      = ( k2_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
 != ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DBjZUDUHrD
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:46:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 30 iterations in 0.031s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(t42_mcart_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( k3_zfmisc_1 @
% 0.21/0.49         ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) =
% 0.21/0.49       ( k2_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_mcart_1 @ A @ B @ D ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49        ( ( k3_zfmisc_1 @
% 0.21/0.49            ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) =
% 0.21/0.49          ( k2_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ ( k3_mcart_1 @ A @ B @ D ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t42_mcart_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B) @ 
% 0.21/0.49         (k2_tarski @ sk_C @ sk_D))
% 0.21/0.49         != (k2_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.49             (k3_mcart_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d3_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         ((k3_mcart_1 @ X8 @ X9 @ X10)
% 0.21/0.49           = (k4_tarski @ (k4_tarski @ X8 @ X9) @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.49  thf(t36_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.21/0.49         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.21/0.49       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.21/0.49         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         ((k2_zfmisc_1 @ (k1_tarski @ X4) @ (k2_tarski @ X5 @ X6))
% 0.21/0.49           = (k2_tarski @ (k4_tarski @ X4 @ X5) @ (k4_tarski @ X4 @ X6)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((k2_zfmisc_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)) @ 
% 0.21/0.49           (k2_tarski @ X0 @ X3))
% 0.21/0.49           = (k2_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 0.21/0.49              (k4_tarski @ (k4_tarski @ X2 @ X1) @ X3)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         ((k3_mcart_1 @ X8 @ X9 @ X10)
% 0.21/0.49           = (k4_tarski @ (k4_tarski @ X8 @ X9) @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((k2_zfmisc_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)) @ 
% 0.21/0.49           (k2_tarski @ X0 @ X3))
% 0.21/0.49           = (k2_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 0.21/0.49              (k3_mcart_1 @ X2 @ X1 @ X3)))),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf(t35_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.49       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         ((k2_zfmisc_1 @ (k1_tarski @ X2) @ (k1_tarski @ X3))
% 0.21/0.49           = (k1_tarski @ (k4_tarski @ X2 @ X3)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.21/0.49  thf(d3_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.21/0.49       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.49         ((k3_zfmisc_1 @ X11 @ X12 @ X13)
% 0.21/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k3_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0) @ X2)
% 0.21/0.49           = (k2_zfmisc_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)) @ X2))),
% 0.21/0.49      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((k3_zfmisc_1 @ (k1_tarski @ X2) @ (k1_tarski @ X1) @ 
% 0.21/0.49           (k2_tarski @ X0 @ X3))
% 0.21/0.49           = (k2_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ 
% 0.21/0.49              (k3_mcart_1 @ X2 @ X1 @ X3)))),
% 0.21/0.49      inference('demod', [status(thm)], ['5', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B) @ 
% 0.21/0.49         (k2_tarski @ sk_C @ sk_D))
% 0.21/0.49         != (k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B) @ 
% 0.21/0.49             (k2_tarski @ sk_C @ sk_D)))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '9'])).
% 0.21/0.49  thf('11', plain, ($false), inference('simplify', [status(thm)], ['10'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
