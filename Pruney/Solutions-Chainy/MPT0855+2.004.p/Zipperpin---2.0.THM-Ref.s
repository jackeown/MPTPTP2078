%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AMYOVAf5oJ

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   31 (  42 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  151 ( 343 expanded)
%              Number of equality atoms :   11 (  23 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t11_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) )
     => ( ! [D: $i,E: $i] :
            ( A
           != ( k4_tarski @ D @ E ) )
        | ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
          & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) )
       => ( ! [D: $i,E: $i] :
              ( A
             != ( k4_tarski @ D @ E ) )
          | ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_mcart_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( sk_A
    = ( k4_tarski @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('4',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_D ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ sk_D @ sk_B ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( sk_A
    = ( k4_tarski @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X5: $i,X7: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X5 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('9',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_E ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ sk_E @ sk_C ),
    inference(demod,[status(thm)],['6','9'])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_E ) @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ ( k4_tarski @ sk_D @ sk_E ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,
    ( sk_A
    = ( k4_tarski @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AMYOVAf5oJ
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:13:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 29 iterations in 0.015s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.48  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.48  thf(t11_mcart_1, conjecture,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.22/0.48         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) =>
% 0.22/0.48       ( ( ![D:$i,E:$i]: ( ( A ) != ( k4_tarski @ D @ E ) ) ) | 
% 0.22/0.48         ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.48        ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.22/0.48            ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) =>
% 0.22/0.48          ( ( ![D:$i,E:$i]: ( ( A ) != ( k4_tarski @ D @ E ) ) ) | 
% 0.22/0.48            ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t11_mcart_1])).
% 0.22/0.48  thf('0', plain, (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('2', plain, (((sk_A) = (k4_tarski @ sk_D @ sk_E))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t7_mcart_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.22/0.48       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X5 : $i, X6 : $i]: ((k1_mcart_1 @ (k4_tarski @ X5 @ X6)) = (X5))),
% 0.22/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.48  thf('4', plain, (((k1_mcart_1 @ sk_A) = (sk_D))),
% 0.22/0.48      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf('5', plain, ((r2_hidden @ sk_D @ sk_B)),
% 0.22/0.48      inference('demod', [status(thm)], ['1', '4'])).
% 0.22/0.48  thf('6', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('7', plain, (((sk_A) = (k4_tarski @ sk_D @ sk_E))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X5 : $i, X7 : $i]: ((k2_mcart_1 @ (k4_tarski @ X5 @ X7)) = (X7))),
% 0.22/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.48  thf('9', plain, (((k2_mcart_1 @ sk_A) = (sk_E))),
% 0.22/0.48      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.48  thf('10', plain, ((r2_hidden @ sk_E @ sk_C)),
% 0.22/0.48      inference('demod', [status(thm)], ['6', '9'])).
% 0.22/0.48  thf(t106_zfmisc_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.48     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.22/0.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 0.22/0.48         ((r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X4))
% 0.22/0.48          | ~ (r2_hidden @ X2 @ X4)
% 0.22/0.48          | ~ (r2_hidden @ X0 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X1 @ X0)
% 0.22/0.48          | (r2_hidden @ (k4_tarski @ X1 @ sk_E) @ (k2_zfmisc_1 @ X0 @ sk_C)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      ((r2_hidden @ (k4_tarski @ sk_D @ sk_E) @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.22/0.48      inference('sup-', [status(thm)], ['5', '12'])).
% 0.22/0.48  thf('14', plain, (((sk_A) = (k4_tarski @ sk_D @ sk_E))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('15', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.22/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.48  thf('16', plain, ($false), inference('demod', [status(thm)], ['0', '15'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
