%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mWh7KhEw5c

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  46 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  187 ( 356 expanded)
%              Number of equality atoms :   27 (  51 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('0',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X5 ) @ X7 )
      | ~ ( r2_hidden @ X5 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('4',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(demod,[status(thm)],['1','7'])).

thf('9',plain,
    ( $false
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ X5 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('12',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('14',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( sk_B != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['17','18'])).

thf('20',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['9','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mWh7KhEw5c
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:27:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 22 iterations in 0.025s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(t14_mcart_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( r2_hidden @
% 0.21/0.50         A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) ) =>
% 0.21/0.50       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.50        ( ( r2_hidden @
% 0.21/0.50            A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) ) =>
% 0.21/0.50          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & ( ( k2_mcart_1 @ A ) = ( C ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t14_mcart_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_C_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((((k2_mcart_1 @ sk_A) != (sk_C_1)))
% 0.21/0.50         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C_1))))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      ((r2_hidden @ sk_A @ 
% 0.21/0.50        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_C_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t10_mcart_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.50       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.50         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         ((r2_hidden @ (k2_mcart_1 @ X5) @ X7)
% 0.21/0.50          | ~ (r2_hidden @ X5 @ (k2_zfmisc_1 @ X6 @ X7)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.50  thf('4', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf(d1_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i, X3 : $i]:
% 0.21/0.50         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.50  thf('7', plain, (((k2_mcart_1 @ sk_A) = (sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      ((((sk_C_1) != (sk_C_1))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_C_1))))),
% 0.21/0.50      inference('demod', [status(thm)], ['1', '7'])).
% 0.21/0.50  thf('9', plain, (($false) <= (~ (((k2_mcart_1 @ sk_A) = (sk_C_1))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      ((r2_hidden @ sk_A @ 
% 0.21/0.50        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_C_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         ((r2_hidden @ (k1_mcart_1 @ X5) @ X6)
% 0.21/0.50          | ~ (r2_hidden @ X5 @ (k2_zfmisc_1 @ X6 @ X7)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.50  thf('12', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i, X3 : $i]:
% 0.21/0.50         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.50  thf('14', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.21/0.50         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      ((((sk_B) != (sk_B))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain, ((((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (~ (((k2_mcart_1 @ sk_A) = (sk_C_1))) | 
% 0.21/0.50       ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('19', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C_1)))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain, ($false),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['9', '19'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
