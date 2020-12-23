%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jO13SdknDS

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  37 expanded)
%              Number of leaves         :   11 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  152 ( 288 expanded)
%              Number of equality atoms :   23 (  43 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t14_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( ( k2_mcart_1 @ A )
          = C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) )
       => ( ( ( k1_mcart_1 @ A )
            = B )
          & ( ( k2_mcart_1 @ A )
            = C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( k2_mcart_1 @ A )
          = C ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k2_mcart_1 @ X4 )
        = X6 )
      | ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ X5 @ ( k1_tarski @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_mcart_1])).

thf('2',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_mcart_1 @ X2 )
        = X1 )
      | ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('7',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('9',plain,
    ( ( sk_B != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('12',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['10','11'])).

thf('13',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['4','12'])).

thf('14',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['2','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jO13SdknDS
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:03:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 9 iterations in 0.009s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.47  thf(t14_mcart_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( r2_hidden @
% 0.21/0.47         A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) ) =>
% 0.21/0.47       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.47        ( ( r2_hidden @
% 0.21/0.47            A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) ) =>
% 0.21/0.47          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & ( ( k2_mcart_1 @ A ) = ( C ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t14_mcart_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((r2_hidden @ sk_A @ 
% 0.21/0.47        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_C)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t13_mcart_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 0.21/0.47       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.47         ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.47         (((k2_mcart_1 @ X4) = (X6))
% 0.21/0.47          | ~ (r2_hidden @ X4 @ (k2_zfmisc_1 @ X5 @ (k1_tarski @ X6))))),
% 0.21/0.47      inference('cnf', [status(esa)], [t13_mcart_1])).
% 0.21/0.47  thf('2', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.21/0.47         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.47      inference('split', [status(esa)], ['3'])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      ((r2_hidden @ sk_A @ 
% 0.21/0.47        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_C)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t12_mcart_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.21/0.47       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.21/0.47         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.47         (((k1_mcart_1 @ X2) = (X1))
% 0.21/0.47          | ~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X3)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.21/0.47  thf('7', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.21/0.47         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['3'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      ((((sk_B) != (sk_B))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf('10', plain, ((((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (~ (((k2_mcart_1 @ sk_A) = (sk_C))) | ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.47      inference('split', [status(esa)], ['3'])).
% 0.21/0.47  thf('12', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain, (((k2_mcart_1 @ sk_A) != (sk_C))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['4', '12'])).
% 0.21/0.47  thf('14', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['2', '13'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
