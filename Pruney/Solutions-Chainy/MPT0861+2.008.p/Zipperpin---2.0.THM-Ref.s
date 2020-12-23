%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o5Jk6pxUAg

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:52 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   41 (  73 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  260 ( 710 expanded)
%              Number of equality atoms :   43 ( 110 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X14 ) @ X15 )
      | ~ ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ( X9 = X8 )
      | ( X9 = X5 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('4',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( X9 = X5 )
      | ( X9 = X8 )
      | ~ ( r2_hidden @ X9 @ ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C_1 )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C_1 )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X14 ) @ X16 )
      | ~ ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('10',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('12',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D_1 ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( sk_D_1 != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D_1 ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C_1 )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('19',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['17','18'])).

thf('20',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C_1 ),
    inference(simpl_trail,[status(thm)],['7','19'])).

thf('21',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf('22',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['14'])).

thf('23',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['17','22'])).

thf('24',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['21','23'])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['5','20','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o5Jk6pxUAg
% 0.13/0.37  % Computer   : n007.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 15:36:36 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.23/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.48  % Solved by: fo/fo7.sh
% 0.23/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.48  % done 38 iterations in 0.018s
% 0.23/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.48  % SZS output start Refutation
% 0.23/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.48  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.23/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.23/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.23/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.48  thf(t17_mcart_1, conjecture,
% 0.23/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.48     ( ( r2_hidden @
% 0.23/0.48         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.23/0.48       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.23/0.48         ( ( k2_mcart_1 @ A ) = ( D ) ) ) ))).
% 0.23/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.48        ( ( r2_hidden @
% 0.23/0.48            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.23/0.48          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.23/0.48            ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) )),
% 0.23/0.48    inference('cnf.neg', [status(esa)], [t17_mcart_1])).
% 0.23/0.48  thf('0', plain,
% 0.23/0.48      ((r2_hidden @ sk_A @ 
% 0.23/0.48        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C_1) @ (k1_tarski @ sk_D_1)))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(t10_mcart_1, axiom,
% 0.23/0.48    (![A:$i,B:$i,C:$i]:
% 0.23/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.23/0.48       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.23/0.48         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.23/0.48  thf('1', plain,
% 0.23/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.48         ((r2_hidden @ (k1_mcart_1 @ X14) @ X15)
% 0.23/0.48          | ~ (r2_hidden @ X14 @ (k2_zfmisc_1 @ X15 @ X16)))),
% 0.23/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.23/0.48  thf('2', plain,
% 0.23/0.48      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C_1))),
% 0.23/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.49  thf(d2_tarski, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.23/0.49       ( ![D:$i]:
% 0.23/0.49         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.23/0.49  thf('3', plain,
% 0.23/0.49      (![X5 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.49         (~ (r2_hidden @ X9 @ X7)
% 0.23/0.49          | ((X9) = (X8))
% 0.23/0.49          | ((X9) = (X5))
% 0.23/0.49          | ((X7) != (k2_tarski @ X8 @ X5)))),
% 0.23/0.49      inference('cnf', [status(esa)], [d2_tarski])).
% 0.23/0.49  thf('4', plain,
% 0.23/0.49      (![X5 : $i, X8 : $i, X9 : $i]:
% 0.23/0.49         (((X9) = (X5))
% 0.23/0.49          | ((X9) = (X8))
% 0.23/0.49          | ~ (r2_hidden @ X9 @ (k2_tarski @ X8 @ X5)))),
% 0.23/0.49      inference('simplify', [status(thm)], ['3'])).
% 0.23/0.49  thf('5', plain,
% 0.23/0.49      ((((k1_mcart_1 @ sk_A) = (sk_B)) | ((k1_mcart_1 @ sk_A) = (sk_C_1)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['2', '4'])).
% 0.23/0.49  thf('6', plain,
% 0.23/0.49      ((((k1_mcart_1 @ sk_A) != (sk_C_1)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('7', plain,
% 0.23/0.49      ((((k1_mcart_1 @ sk_A) != (sk_C_1)))
% 0.23/0.49         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C_1))))),
% 0.23/0.49      inference('split', [status(esa)], ['6'])).
% 0.23/0.49  thf('8', plain,
% 0.23/0.49      ((r2_hidden @ sk_A @ 
% 0.23/0.49        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C_1) @ (k1_tarski @ sk_D_1)))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('9', plain,
% 0.23/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.49         ((r2_hidden @ (k2_mcart_1 @ X14) @ X16)
% 0.23/0.49          | ~ (r2_hidden @ X14 @ (k2_zfmisc_1 @ X15 @ X16)))),
% 0.23/0.49      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.23/0.49  thf('10', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_D_1))),
% 0.23/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.49  thf(d1_tarski, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.23/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.23/0.49  thf('11', plain,
% 0.23/0.49      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.23/0.49         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.23/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.23/0.49  thf('12', plain,
% 0.23/0.49      (![X0 : $i, X3 : $i]:
% 0.23/0.49         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.23/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.23/0.49  thf('13', plain, (((k2_mcart_1 @ sk_A) = (sk_D_1))),
% 0.23/0.49      inference('sup-', [status(thm)], ['10', '12'])).
% 0.23/0.49  thf('14', plain,
% 0.23/0.49      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('15', plain,
% 0.23/0.49      ((((k2_mcart_1 @ sk_A) != (sk_D_1)))
% 0.23/0.49         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.23/0.49      inference('split', [status(esa)], ['14'])).
% 0.23/0.49  thf('16', plain,
% 0.23/0.49      ((((sk_D_1) != (sk_D_1))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.23/0.49      inference('sup-', [status(thm)], ['13', '15'])).
% 0.23/0.49  thf('17', plain, ((((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.23/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.23/0.49  thf('18', plain,
% 0.23/0.49      (~ (((k1_mcart_1 @ sk_A) = (sk_C_1))) | 
% 0.23/0.49       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.23/0.49      inference('split', [status(esa)], ['6'])).
% 0.23/0.49  thf('19', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_C_1)))),
% 0.23/0.49      inference('sat_resolution*', [status(thm)], ['17', '18'])).
% 0.23/0.49  thf('20', plain, (((k1_mcart_1 @ sk_A) != (sk_C_1))),
% 0.23/0.49      inference('simpl_trail', [status(thm)], ['7', '19'])).
% 0.23/0.49  thf('21', plain,
% 0.23/0.49      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.23/0.49         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.23/0.49      inference('split', [status(esa)], ['14'])).
% 0.23/0.49  thf('22', plain,
% 0.23/0.49      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.23/0.49       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.23/0.49      inference('split', [status(esa)], ['14'])).
% 0.23/0.49  thf('23', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.23/0.49      inference('sat_resolution*', [status(thm)], ['17', '22'])).
% 0.23/0.49  thf('24', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.23/0.49      inference('simpl_trail', [status(thm)], ['21', '23'])).
% 0.23/0.49  thf('25', plain, ($false),
% 0.23/0.49      inference('simplify_reflect-', [status(thm)], ['5', '20', '24'])).
% 0.23/0.49  
% 0.23/0.49  % SZS output end Refutation
% 0.23/0.49  
% 0.23/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
