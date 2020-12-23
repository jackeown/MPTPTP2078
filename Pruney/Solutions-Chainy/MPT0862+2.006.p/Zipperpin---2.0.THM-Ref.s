%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZdhInieTdo

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  69 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  240 ( 677 expanded)
%              Number of equality atoms :   39 ( 106 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t18_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) )
       => ( ( ( k1_mcart_1 @ A )
            = B )
          & ( ( ( k2_mcart_1 @ A )
              = C )
            | ( ( k2_mcart_1 @ A )
              = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_mcart_1 @ X9 )
        = X12 )
      | ( ( k2_mcart_1 @ X9 )
        = X11 )
      | ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X10 @ ( k2_tarski @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_mcart_1])).

thf('2',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C_1 )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X6 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('7',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('9',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( sk_B != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('16',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D ),
    inference('sat_resolution*',[status(thm)],['14','15'])).

thf('17',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D ),
    inference(simpl_trail,[status(thm)],['4','16'])).

thf('18',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('19',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C_1 )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('20',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['14','19'])).

thf('21',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C_1 ),
    inference(simpl_trail,[status(thm)],['18','20'])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['2','17','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZdhInieTdo
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 30 iterations in 0.026s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(t18_mcart_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( r2_hidden @
% 0.21/0.48         A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.21/0.48       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.21/0.48         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48        ( ( r2_hidden @
% 0.21/0.48            A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.21/0.48          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.21/0.48            ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t18_mcart_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((r2_hidden @ sk_A @ 
% 0.21/0.48        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C_1 @ sk_D)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t16_mcart_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.21/0.48       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.48         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.48         (((k2_mcart_1 @ X9) = (X12))
% 0.21/0.48          | ((k2_mcart_1 @ X9) = (X11))
% 0.21/0.48          | ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X10 @ (k2_tarski @ X11 @ X12))))),
% 0.21/0.48      inference('cnf', [status(esa)], [t16_mcart_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((((k2_mcart_1 @ sk_A) = (sk_C_1)) | ((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      ((((k2_mcart_1 @ sk_A) != (sk_D)))
% 0.21/0.48         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      ((r2_hidden @ sk_A @ 
% 0.21/0.48        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C_1 @ sk_D)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t10_mcart_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.48       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.48         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.48         ((r2_hidden @ (k1_mcart_1 @ X6) @ X7)
% 0.21/0.48          | ~ (r2_hidden @ X6 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.48  thf('7', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf(d1_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i, X3 : $i]:
% 0.21/0.48         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.48  thf('10', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_C_1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.21/0.48         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      ((((sk_B) != (sk_B))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.48  thf('14', plain, ((((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (~ (((k2_mcart_1 @ sk_A) = (sk_D))) | ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('16', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('17', plain, (((k2_mcart_1 @ sk_A) != (sk_D))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['4', '16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      ((((k2_mcart_1 @ sk_A) != (sk_C_1)))
% 0.21/0.48         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C_1))))),
% 0.21/0.48      inference('split', [status(esa)], ['11'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (~ (((k2_mcart_1 @ sk_A) = (sk_C_1))) | 
% 0.21/0.48       ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['11'])).
% 0.21/0.48  thf('20', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C_1)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['14', '19'])).
% 0.21/0.48  thf('21', plain, (((k2_mcart_1 @ sk_A) != (sk_C_1))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['18', '20'])).
% 0.21/0.48  thf('22', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['2', '17', '21'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
