%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YL3Pl0HjAU

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   41 (  59 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  284 ( 505 expanded)
%              Number of equality atoms :   19 (  35 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

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

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X6 ) @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ ( k1_tarski @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X6 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('5',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t11_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) )
     => ( ! [D: $i,E: $i] :
            ( A
           != ( k4_tarski @ D @ E ) )
        | ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11
       != ( k4_tarski @ X9 @ X10 ) )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ X11 ) @ X12 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ X11 ) @ X13 )
      | ( r2_hidden @ X11 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t11_mcart_1])).

thf('7',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k2_zfmisc_1 @ X12 @ X13 ) )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k4_tarski @ X9 @ X10 ) ) @ X13 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ ( k4_tarski @ X9 @ X10 ) ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('8',plain,(
    ! [X17: $i,X19: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X17 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('10',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k2_zfmisc_1 @ X12 @ X13 ) )
      | ~ ( r2_hidden @ X10 @ X13 )
      | ~ ( r2_hidden @ X9 @ X12 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    r2_hidden @ ( k4_tarski @ ( k2_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_mcart_1 @ X15 )
        = X14 )
      | ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ ( k1_tarski @ X14 ) @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('14',plain,
    ( ( k1_mcart_1 @ ( k4_tarski @ ( k2_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) )
    = sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('16',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('20',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('21',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('23',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['21','22'])).

thf('24',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['18','23'])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['16','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YL3Pl0HjAU
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 28 iterations in 0.014s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.46  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.46  thf(t13_mcart_1, conjecture,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 0.19/0.46       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.19/0.46         ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.46        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 0.19/0.46          ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.19/0.46            ( ( k2_mcart_1 @ A ) = ( C ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t13_mcart_1])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k1_tarski @ sk_C)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t10_mcart_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.19/0.46       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.19/0.46         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.46         ((r2_hidden @ (k2_mcart_1 @ X6) @ X8)
% 0.19/0.46          | ~ (r2_hidden @ X6 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.19/0.46  thf('2', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ (k1_tarski @ sk_C)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.46         ((r2_hidden @ (k1_mcart_1 @ X6) @ X7)
% 0.19/0.46          | ~ (r2_hidden @ X6 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.19/0.46  thf('5', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.19/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.46  thf(t11_mcart_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.19/0.46         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) =>
% 0.19/0.46       ( ( ![D:$i,E:$i]: ( ( A ) != ( k4_tarski @ D @ E ) ) ) | 
% 0.19/0.46         ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.46         (((X11) != (k4_tarski @ X9 @ X10))
% 0.19/0.46          | ~ (r2_hidden @ (k1_mcart_1 @ X11) @ X12)
% 0.19/0.46          | ~ (r2_hidden @ (k2_mcart_1 @ X11) @ X13)
% 0.19/0.46          | (r2_hidden @ X11 @ (k2_zfmisc_1 @ X12 @ X13)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t11_mcart_1])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X9 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 0.19/0.46         ((r2_hidden @ (k4_tarski @ X9 @ X10) @ (k2_zfmisc_1 @ X12 @ X13))
% 0.19/0.46          | ~ (r2_hidden @ (k2_mcart_1 @ (k4_tarski @ X9 @ X10)) @ X13)
% 0.19/0.46          | ~ (r2_hidden @ (k1_mcart_1 @ (k4_tarski @ X9 @ X10)) @ X12))),
% 0.19/0.46      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.46  thf(t7_mcart_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.19/0.46       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X17 : $i, X19 : $i]: ((k2_mcart_1 @ (k4_tarski @ X17 @ X19)) = (X19))),
% 0.19/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      (![X17 : $i, X18 : $i]: ((k1_mcart_1 @ (k4_tarski @ X17 @ X18)) = (X17))),
% 0.19/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.46  thf('10', plain,
% 0.19/0.46      (![X9 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 0.19/0.46         ((r2_hidden @ (k4_tarski @ X9 @ X10) @ (k2_zfmisc_1 @ X12 @ X13))
% 0.19/0.46          | ~ (r2_hidden @ X10 @ X13)
% 0.19/0.46          | ~ (r2_hidden @ X9 @ X12))),
% 0.19/0.46      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X1 @ X0)
% 0.19/0.46          | (r2_hidden @ (k4_tarski @ X1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.19/0.46             (k2_zfmisc_1 @ X0 @ sk_B)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['5', '10'])).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      ((r2_hidden @ (k4_tarski @ (k2_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A)) @ 
% 0.19/0.46        (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['2', '11'])).
% 0.19/0.46  thf(t12_mcart_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.19/0.46       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.19/0.46         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.46         (((k1_mcart_1 @ X15) = (X14))
% 0.19/0.46          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ (k1_tarski @ X14) @ X16)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (((k1_mcart_1 @ (k4_tarski @ (k2_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A)))
% 0.19/0.46         = (sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      (![X17 : $i, X18 : $i]: ((k1_mcart_1 @ (k4_tarski @ X17 @ X18)) = (X17))),
% 0.19/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.46  thf('16', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.19/0.46      inference('demod', [status(thm)], ['14', '15'])).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.19/0.46        | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.19/0.46         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.19/0.46      inference('split', [status(esa)], ['17'])).
% 0.19/0.46  thf('19', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.19/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.46  thf('20', plain,
% 0.19/0.46      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))
% 0.19/0.46         <= (~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)))),
% 0.19/0.46      inference('split', [status(esa)], ['17'])).
% 0.19/0.46  thf('21', plain, (((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.46  thf('22', plain,
% 0.19/0.46      (~ (((k2_mcart_1 @ sk_A) = (sk_C))) | 
% 0.19/0.46       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.19/0.46      inference('split', [status(esa)], ['17'])).
% 0.19/0.46  thf('23', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.19/0.46      inference('sat_resolution*', [status(thm)], ['21', '22'])).
% 0.19/0.46  thf('24', plain, (((k2_mcart_1 @ sk_A) != (sk_C))),
% 0.19/0.46      inference('simpl_trail', [status(thm)], ['18', '23'])).
% 0.19/0.46  thf('25', plain, ($false),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['16', '24'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
