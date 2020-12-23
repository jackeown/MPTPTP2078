%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BTG0cqTeKH

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:48 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   37 (  61 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  205 ( 471 expanded)
%              Number of equality atoms :   36 (  73 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(t67_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_mcart_1])).

thf('0',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X0 ) @ ( sk_E @ X0 ) )
        = X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('4',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X3
       != ( k2_mcart_1 @ X3 ) )
      | ( X3
       != ( k4_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_tarski @ X4 @ X5 )
     != ( k2_mcart_1 @ ( k4_tarski @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
 != ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('9',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( $false
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['1','9'])).

thf('11',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X3
       != ( k1_mcart_1 @ X3 ) )
      | ( X3
       != ( k4_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_tarski @ X4 @ X5 )
     != ( k1_mcart_1 @ ( k4_tarski @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
 != ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('17',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['10','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BTG0cqTeKH
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 10 iterations in 0.009s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.46  thf(sk_E_type, type, sk_E: $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.46  thf(sk_D_type, type, sk_D: $i > $i).
% 0.19/0.46  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.46  thf(t67_mcart_1, conjecture,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.19/0.46       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.46        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.19/0.46          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t67_mcart_1])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.46      inference('split', [status(esa)], ['0'])).
% 0.19/0.46  thf('2', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(l139_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.19/0.46          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (((k4_tarski @ (sk_D @ X0) @ (sk_E @ X0)) = (X0))
% 0.19/0.46          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.19/0.46      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.19/0.46  thf('4', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.46  thf(t20_mcart_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.19/0.46       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.46         (((X3) != (k2_mcart_1 @ X3)) | ((X3) != (k4_tarski @ X4 @ X5)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X4 : $i, X5 : $i]:
% 0.19/0.46         ((k4_tarski @ X4 @ X5) != (k2_mcart_1 @ (k4_tarski @ X4 @ X5)))),
% 0.19/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) != (k2_mcart_1 @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['4', '6'])).
% 0.19/0.46  thf('8', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.46  thf('9', plain, (((sk_A) != (k2_mcart_1 @ sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.46  thf('10', plain, (($false) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['1', '9'])).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.46      inference('split', [status(esa)], ['0'])).
% 0.19/0.46  thf('12', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.46         (((X3) != (k1_mcart_1 @ X3)) | ((X3) != (k4_tarski @ X4 @ X5)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (![X4 : $i, X5 : $i]:
% 0.19/0.46         ((k4_tarski @ X4 @ X5) != (k1_mcart_1 @ (k4_tarski @ X4 @ X5)))),
% 0.19/0.46      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) != (k1_mcart_1 @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['12', '14'])).
% 0.19/0.46  thf('16', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.46  thf('17', plain, (((sk_A) != (k1_mcart_1 @ sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      ((((sk_A) != (sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['11', '17'])).
% 0.19/0.46  thf('19', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.19/0.46      inference('simplify', [status(thm)], ['18'])).
% 0.19/0.46  thf('20', plain,
% 0.19/0.46      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.19/0.46      inference('split', [status(esa)], ['0'])).
% 0.19/0.46  thf('21', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.19/0.46      inference('sat_resolution*', [status(thm)], ['19', '20'])).
% 0.19/0.46  thf('22', plain, ($false),
% 0.19/0.46      inference('simpl_trail', [status(thm)], ['10', '21'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
