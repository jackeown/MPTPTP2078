%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PIBqk4tD3S

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  53 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  192 ( 400 expanded)
%              Number of equality atoms :   34 (  63 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) )
      = ( k1_tarski @ ( k4_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

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
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('8',plain,(
    ! [X7: $i,X9: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X7 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('9',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(demod,[status(thm)],['1','9'])).

thf('11',plain,
    ( $false
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('14',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['12','13'])).

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
    inference(simpl_trail,[status(thm)],['11','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PIBqk4tD3S
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:31:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 13 iterations in 0.012s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.48  thf(t14_mcart_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( r2_hidden @
% 0.21/0.48         A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) ) =>
% 0.21/0.48       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.48        ( ( r2_hidden @
% 0.21/0.48            A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) ) =>
% 0.21/0.48          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & ( ( k2_mcart_1 @ A ) = ( C ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t14_mcart_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_C_1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((((k2_mcart_1 @ sk_A) != (sk_C_1)))
% 0.21/0.48         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C_1))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((r2_hidden @ sk_A @ 
% 0.21/0.48        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_C_1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t35_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.48       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]:
% 0.21/0.48         ((k2_zfmisc_1 @ (k1_tarski @ X5) @ (k1_tarski @ X6))
% 0.21/0.48           = (k1_tarski @ (k4_tarski @ X5 @ X6)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      ((r2_hidden @ sk_A @ (k1_tarski @ (k4_tarski @ sk_B @ sk_C_1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf(d1_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i, X3 : $i]:
% 0.21/0.48         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.48  thf('7', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.48  thf(t7_mcart_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.48       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X7 : $i, X9 : $i]: ((k2_mcart_1 @ (k4_tarski @ X7 @ X9)) = (X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.48  thf('9', plain, (((k2_mcart_1 @ sk_A) = (sk_C_1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      ((((sk_C_1) != (sk_C_1))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_C_1))))),
% 0.21/0.48      inference('demod', [status(thm)], ['1', '9'])).
% 0.21/0.48  thf('11', plain, (($false) <= (~ (((k2_mcart_1 @ sk_A) = (sk_C_1))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.48  thf('12', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]: ((k1_mcart_1 @ (k4_tarski @ X7 @ X8)) = (X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.48  thf('14', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.21/0.48      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.21/0.48         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((((sk_B) != (sk_B))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('17', plain, ((((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (~ (((k2_mcart_1 @ sk_A) = (sk_C_1))) | 
% 0.21/0.48       ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('19', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C_1)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain, ($false),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['11', '19'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
