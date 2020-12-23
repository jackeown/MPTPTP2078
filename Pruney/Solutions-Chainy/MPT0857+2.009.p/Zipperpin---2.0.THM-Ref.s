%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TixTvrl8eJ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  76 expanded)
%              Number of leaves         :   16 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  247 ( 620 expanded)
%              Number of equality atoms :   25 (  57 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t13_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( k2_mcart_1 @ A )
          = C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
       => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
          & ( ( k2_mcart_1 @ A )
            = C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k1_tarski @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k1_tarski @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X6 ) @ ( sk_E @ X6 ) )
        = X6 )
      | ~ ( r2_hidden @ X6 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('3',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('6',plain,
    ( ( k1_mcart_1 @ sk_A )
    = ( sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['3','6'])).

thf('9',plain,(
    ! [X17: $i,X19: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X17 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('10',plain,
    ( ( k2_mcart_1 @ sk_A )
    = ( sk_E @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['7','10'])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X11 = X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ ( k1_tarski @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k2_mcart_1 @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k1_tarski @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X14 ) @ X15 )
      | ~ ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('19',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('21',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('23',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['21','22'])).

thf('24',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['16','23'])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TixTvrl8eJ
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:19:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 36 iterations in 0.019s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i > $i).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.47  thf(sk_E_type, type, sk_E: $i > $i).
% 0.21/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.47  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(t13_mcart_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 0.21/0.47       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.47         ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.47        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 0.21/0.47          ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.47            ( ( k2_mcart_1 @ A ) = ( C ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t13_mcart_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k1_tarski @ sk_C)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k1_tarski @ sk_C)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(l139_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.47          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.47         (((k4_tarski @ (sk_D @ X6) @ (sk_E @ X6)) = (X6))
% 0.21/0.47          | ~ (r2_hidden @ X6 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.21/0.47  thf('3', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf(t7_mcart_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.47       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X17 : $i, X18 : $i]: ((k1_mcart_1 @ (k4_tarski @ X17 @ X18)) = (X17))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.47  thf('6', plain, (((k1_mcart_1 @ sk_A) = (sk_D @ sk_A))),
% 0.21/0.47      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '6'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X17 : $i, X19 : $i]: ((k2_mcart_1 @ (k4_tarski @ X17 @ X19)) = (X19))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.47  thf('10', plain, (((k2_mcart_1 @ sk_A) = (sk_E @ sk_A))),
% 0.21/0.47      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)) = (sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '10'])).
% 0.21/0.47  thf(t129_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( r2_hidden @
% 0.21/0.47         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.21/0.47       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.47         (((X11) = (X12))
% 0.21/0.47          | ~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ 
% 0.21/0.47               (k2_zfmisc_1 @ X10 @ (k1_tarski @ X12))))),
% 0.21/0.47      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0)))
% 0.21/0.47          | ((k2_mcart_1 @ sk_A) = (X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('14', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.21/0.47        | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.21/0.47         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.47      inference('split', [status(esa)], ['15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k1_tarski @ sk_C)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t10_mcart_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.47       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.47         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.47         ((r2_hidden @ (k1_mcart_1 @ X14) @ X15)
% 0.21/0.47          | ~ (r2_hidden @ X14 @ (k2_zfmisc_1 @ X15 @ X16)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.47  thf('19', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.21/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))
% 0.21/0.47         <= (~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)))),
% 0.21/0.47      inference('split', [status(esa)], ['15'])).
% 0.21/0.47  thf('21', plain, (((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (~ (((k2_mcart_1 @ sk_A) = (sk_C))) | 
% 0.21/0.47       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.21/0.47      inference('split', [status(esa)], ['15'])).
% 0.21/0.47  thf('23', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf('24', plain, (((k2_mcart_1 @ sk_A) != (sk_C))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['16', '23'])).
% 0.21/0.47  thf('25', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['14', '24'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
