%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6r1HyPQqbX

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  69 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  240 ( 677 expanded)
%              Number of equality atoms :   39 ( 106 expanded)
%              Maximal formula depth    :   13 (   5 average)

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

thf(t17_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( ( k2_mcart_1 @ A )
          = D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( ( k2_mcart_1 @ A )
            = D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_mcart_1 @ X10 )
        = X9 )
      | ( ( k1_mcart_1 @ X10 )
        = X11 )
      | ~ ( r2_hidden @ X10 @ ( k2_zfmisc_1 @ ( k2_tarski @ X11 @ X9 ) @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t15_mcart_1])).

thf('2',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C_1 )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C_1 )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X6 ) @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('7',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_D ) ),
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
    ( ( k2_mcart_1 @ sk_A )
    = sk_D ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( sk_D != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C_1 )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['3'])).

thf('16',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['14','15'])).

thf('17',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C_1 ),
    inference(simpl_trail,[status(thm)],['4','16'])).

thf('18',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('19',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['11'])).

thf('20',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['14','19'])).

thf('21',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['18','20'])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['2','17','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6r1HyPQqbX
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:18:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 30 iterations in 0.037s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(t17_mcart_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( r2_hidden @
% 0.22/0.50         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.22/0.50       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.22/0.50         ( ( k2_mcart_1 @ A ) = ( D ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50        ( ( r2_hidden @
% 0.22/0.50            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.22/0.50          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.22/0.50            ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t17_mcart_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((r2_hidden @ sk_A @ 
% 0.22/0.50        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C_1) @ (k1_tarski @ sk_D)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t15_mcart_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 0.22/0.50       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.22/0.50         ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.50         (((k1_mcart_1 @ X10) = (X9))
% 0.22/0.50          | ((k1_mcart_1 @ X10) = (X11))
% 0.22/0.50          | ~ (r2_hidden @ X10 @ (k2_zfmisc_1 @ (k2_tarski @ X11 @ X9) @ X12)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t15_mcart_1])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      ((((k1_mcart_1 @ sk_A) = (sk_B)) | ((k1_mcart_1 @ sk_A) = (sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      ((((k1_mcart_1 @ sk_A) != (sk_C_1)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      ((((k1_mcart_1 @ sk_A) != (sk_C_1)))
% 0.22/0.50         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C_1))))),
% 0.22/0.50      inference('split', [status(esa)], ['3'])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      ((r2_hidden @ sk_A @ 
% 0.22/0.50        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C_1) @ (k1_tarski @ sk_D)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t10_mcart_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.22/0.50       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.22/0.50         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.50         ((r2_hidden @ (k2_mcart_1 @ X6) @ X8)
% 0.22/0.50          | ~ (r2_hidden @ X6 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.50  thf('7', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_D))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf(d1_tarski, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X0 : $i, X3 : $i]:
% 0.22/0.50         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.50  thf('10', plain, (((k2_mcart_1 @ sk_A) = (sk_D))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      ((((k2_mcart_1 @ sk_A) != (sk_D)))
% 0.22/0.50         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.22/0.50      inference('split', [status(esa)], ['11'])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      ((((sk_D) != (sk_D))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '12'])).
% 0.22/0.50  thf('14', plain, ((((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (~ (((k1_mcart_1 @ sk_A) = (sk_C_1))) | 
% 0.22/0.50       ~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.22/0.50      inference('split', [status(esa)], ['3'])).
% 0.22/0.50  thf('16', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_C_1)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['14', '15'])).
% 0.22/0.50  thf('17', plain, (((k1_mcart_1 @ sk_A) != (sk_C_1))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['4', '16'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.22/0.50         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.22/0.50      inference('split', [status(esa)], ['11'])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | ~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.22/0.50      inference('split', [status(esa)], ['11'])).
% 0.22/0.50  thf('20', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['14', '19'])).
% 0.22/0.50  thf('21', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['18', '20'])).
% 0.22/0.50  thf('22', plain, ($false),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['2', '17', '21'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
