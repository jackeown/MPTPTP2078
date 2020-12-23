%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9M96dO1xwL

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  31 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  223 ( 283 expanded)
%              Number of equality atoms :   25 (  36 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

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
    ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 )
 != ( k3_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X11 @ X12 ) @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_mcart_1 @ X11 @ X12 @ X13 @ X14 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X11 @ X12 ) @ X13 ) @ X14 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_mcart_1 @ X7 @ X8 @ X9 @ X10 )
      = ( k4_tarski @ ( k3_mcart_1 @ X7 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf(d1_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ! [B: $i] :
          ( ( B
            = ( k1_mcart_1 @ A ) )
        <=> ! [C: $i,D: $i] :
              ( ( A
                = ( k4_tarski @ C @ D ) )
             => ( B = C ) ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4
       != ( k1_mcart_1 @ X1 ) )
      | ( X4 = X5 )
      | ( X1
       != ( k4_tarski @ X5 @ X6 ) )
      | ( X1
       != ( k4_tarski @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_mcart_1])).

thf('6',plain,(
    ! [X2: $i,X3: $i,X5: $i,X6: $i] :
      ( ( ( k4_tarski @ X5 @ X6 )
       != ( k4_tarski @ X2 @ X3 ) )
      | ( ( k1_mcart_1 @ ( k4_tarski @ X5 @ X6 ) )
        = X5 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( k4_mcart_1 @ X4 @ X3 @ X2 @ X1 ) @ X0 ) )
      = ( k3_mcart_1 @ ( k4_tarski @ X4 @ X3 ) @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_mcart_1 @ X4 @ X3 @ X2 @ X1 )
      = ( k3_mcart_1 @ ( k4_tarski @ X4 @ X3 ) @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 )
 != ( k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','11'])).

thf('13',plain,(
    $false ),
    inference(simplify,[status(thm)],['12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9M96dO1xwL
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 9 iterations in 0.018s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.47  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.47  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.47  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.47  thf(t32_mcart_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.47       ( k3_mcart_1 @ ( k4_tarski @ A @ B ) @ C @ D ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47        ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.47          ( k3_mcart_1 @ ( k4_tarski @ A @ B ) @ C @ D ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t32_mcart_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1)
% 0.20/0.47         != (k3_mcart_1 @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1 @ sk_D_1))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t31_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.47       ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.47         ((k4_mcart_1 @ X11 @ X12 @ X13 @ X14)
% 0.20/0.47           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X11 @ X12) @ X13) @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.47         ((k4_mcart_1 @ X11 @ X12 @ X13 @ X14)
% 0.20/0.47           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X11 @ X12) @ X13) @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         ((k4_mcart_1 @ (k4_tarski @ X3 @ X2) @ X1 @ X0 @ X4)
% 0.20/0.47           = (k4_tarski @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 0.20/0.47      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf(d4_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.47       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.47         ((k4_mcart_1 @ X7 @ X8 @ X9 @ X10)
% 0.20/0.47           = (k4_tarski @ (k3_mcart_1 @ X7 @ X8 @ X9) @ X10))),
% 0.20/0.47      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.20/0.47  thf(d1_mcart_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( B ) = ( k1_mcart_1 @ A ) ) <=>
% 0.20/0.47           ( ![C:$i,D:$i]:
% 0.20/0.47             ( ( ( A ) = ( k4_tarski @ C @ D ) ) => ( ( B ) = ( C ) ) ) ) ) ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         (((X4) != (k1_mcart_1 @ X1))
% 0.20/0.47          | ((X4) = (X5))
% 0.20/0.47          | ((X1) != (k4_tarski @ X5 @ X6))
% 0.20/0.47          | ((X1) != (k4_tarski @ X2 @ X3)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_mcart_1])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         (((k4_tarski @ X5 @ X6) != (k4_tarski @ X2 @ X3))
% 0.20/0.47          | ((k1_mcart_1 @ (k4_tarski @ X5 @ X6)) = (X5)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: ((k1_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X1))),
% 0.20/0.47      inference('eq_res', [status(thm)], ['6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.47           = (k3_mcart_1 @ X3 @ X2 @ X1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['4', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         ((k1_mcart_1 @ (k4_tarski @ (k4_mcart_1 @ X4 @ X3 @ X2 @ X1) @ X0))
% 0.20/0.47           = (k3_mcart_1 @ (k4_tarski @ X4 @ X3) @ X2 @ X1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['3', '8'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: ((k1_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X1))),
% 0.20/0.47      inference('eq_res', [status(thm)], ['6'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         ((k4_mcart_1 @ X4 @ X3 @ X2 @ X1)
% 0.20/0.47           = (k3_mcart_1 @ (k4_tarski @ X4 @ X3) @ X2 @ X1))),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (((k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1)
% 0.20/0.47         != (k4_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1))),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '11'])).
% 0.20/0.47  thf('13', plain, ($false), inference('simplify', [status(thm)], ['12'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
