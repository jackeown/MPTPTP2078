%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1R0SScFA1N

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:06 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   66 (  86 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  446 ( 691 expanded)
%              Number of equality atoms :   33 (  68 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7 = X6 )
      | ( r2_hidden @ ( sk_C_1 @ X6 @ X7 ) @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X6 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('4',plain,(
    ! [X15: $i] :
      ( r1_xboole_0 @ X15 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('5',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ ( k2_zfmisc_1 @ X17 @ X20 ) )
      | ~ ( r2_hidden @ X18 @ X20 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t114_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ B @ A ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ B @ A ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_zfmisc_1])).

thf('11',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ ( k2_zfmisc_1 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( k1_xboole_0 = sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['18'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('25',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ ( k2_zfmisc_1 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ sk_B )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ sk_B )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['24','36'])).

thf('38',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    sk_B = sk_A ),
    inference('sup+',[status(thm)],['23','41'])).

thf('43',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1R0SScFA1N
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:59:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 276 iterations in 0.156s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.62  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.38/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(t2_tarski, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.38/0.62       ( ( A ) = ( B ) ) ))).
% 0.38/0.62  thf('0', plain,
% 0.38/0.62      (![X6 : $i, X7 : $i]:
% 0.38/0.62         (((X7) = (X6))
% 0.38/0.62          | (r2_hidden @ (sk_C_1 @ X6 @ X7) @ X6)
% 0.38/0.62          | (r2_hidden @ (sk_C_1 @ X6 @ X7) @ X7))),
% 0.38/0.62      inference('cnf', [status(esa)], [t2_tarski])).
% 0.38/0.62  thf(t2_boole, axiom,
% 0.38/0.62    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.38/0.62  thf('1', plain,
% 0.38/0.62      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [t2_boole])).
% 0.38/0.62  thf(t4_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.38/0.62            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.62  thf('2', plain,
% 0.38/0.62      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.38/0.62          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.38/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.38/0.62  thf('3', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.62  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.38/0.62  thf('4', plain, (![X15 : $i]: (r1_xboole_0 @ X15 @ k1_xboole_0)),
% 0.38/0.62      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.38/0.62  thf('5', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.38/0.62      inference('demod', [status(thm)], ['3', '4'])).
% 0.38/0.62  thf('6', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.38/0.62          | ((k1_xboole_0) = (X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['0', '5'])).
% 0.38/0.62  thf(d3_tarski, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.62  thf('7', plain,
% 0.38/0.62      (![X3 : $i, X5 : $i]:
% 0.38/0.62         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.62  thf(l54_zfmisc_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.62     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.38/0.62       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.38/0.62  thf('8', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i, X18 : $i, X20 : $i]:
% 0.38/0.62         ((r2_hidden @ (k4_tarski @ X16 @ X18) @ (k2_zfmisc_1 @ X17 @ X20))
% 0.38/0.62          | ~ (r2_hidden @ X18 @ X20)
% 0.38/0.62          | ~ (r2_hidden @ X16 @ X17))),
% 0.38/0.62      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.38/0.62  thf('9', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.62         ((r1_tarski @ X0 @ X1)
% 0.38/0.62          | ~ (r2_hidden @ X3 @ X2)
% 0.38/0.62          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.38/0.62             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.62  thf('10', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (((k1_xboole_0) = (X0))
% 0.38/0.62          | (r2_hidden @ 
% 0.38/0.62             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ (sk_C @ X2 @ X1)) @ 
% 0.38/0.62             (k2_zfmisc_1 @ X0 @ X1))
% 0.38/0.62          | (r1_tarski @ X1 @ X2))),
% 0.38/0.62      inference('sup-', [status(thm)], ['6', '9'])).
% 0.38/0.62  thf(t114_zfmisc_1, conjecture,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.38/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.38/0.62         ( ( A ) = ( B ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i,B:$i]:
% 0.38/0.62        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.38/0.62          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.38/0.62            ( ( A ) = ( B ) ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 0.38/0.62  thf('11', plain,
% 0.38/0.62      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('12', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.62         ((r2_hidden @ X18 @ X19)
% 0.38/0.62          | ~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ (k2_zfmisc_1 @ X17 @ X19)))),
% 0.38/0.62      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.38/0.62  thf('13', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.38/0.62          | (r2_hidden @ X0 @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.62  thf('14', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r1_tarski @ sk_B @ X0)
% 0.38/0.62          | ((k1_xboole_0) = (sk_A))
% 0.38/0.62          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['10', '13'])).
% 0.38/0.62  thf('15', plain, (((sk_A) != (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('16', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.38/0.62  thf('17', plain,
% 0.38/0.62      (![X3 : $i, X5 : $i]:
% 0.38/0.62         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.62  thf('18', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.62  thf('19', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.38/0.62      inference('simplify', [status(thm)], ['18'])).
% 0.38/0.62  thf(t28_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.62  thf('20', plain,
% 0.38/0.62      (![X12 : $i, X13 : $i]:
% 0.38/0.62         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.38/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.62  thf('21', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.62  thf('23', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.62  thf('24', plain,
% 0.38/0.62      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [t2_boole])).
% 0.38/0.62  thf('25', plain,
% 0.38/0.62      (![X3 : $i, X5 : $i]:
% 0.38/0.62         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.62  thf('26', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.62         ((r1_tarski @ X0 @ X1)
% 0.38/0.62          | ~ (r2_hidden @ X3 @ X2)
% 0.38/0.62          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.38/0.62             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.62  thf('27', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.62         ((r1_tarski @ X0 @ X1)
% 0.38/0.62          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ 
% 0.38/0.62             (k2_zfmisc_1 @ X0 @ X2))
% 0.38/0.62          | (r1_tarski @ X2 @ X3))),
% 0.38/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.62  thf('28', plain,
% 0.38/0.62      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('29', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.62         ((r2_hidden @ X16 @ X17)
% 0.38/0.62          | ~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ (k2_zfmisc_1 @ X17 @ X19)))),
% 0.38/0.62      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.38/0.62  thf('30', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.38/0.62          | (r2_hidden @ X1 @ sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.62  thf('31', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((r1_tarski @ sk_B @ X0)
% 0.38/0.62          | (r1_tarski @ sk_A @ X1)
% 0.38/0.62          | (r2_hidden @ (sk_C @ X1 @ sk_A) @ sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['27', '30'])).
% 0.38/0.62  thf('32', plain,
% 0.38/0.62      (![X3 : $i, X5 : $i]:
% 0.38/0.62         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.62  thf('33', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r1_tarski @ sk_A @ sk_B)
% 0.38/0.62          | (r1_tarski @ sk_B @ X0)
% 0.38/0.62          | (r1_tarski @ sk_A @ sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.62  thf('34', plain,
% 0.38/0.62      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | (r1_tarski @ sk_A @ sk_B))),
% 0.38/0.62      inference('simplify', [status(thm)], ['33'])).
% 0.38/0.62  thf('35', plain,
% 0.38/0.62      (![X12 : $i, X13 : $i]:
% 0.38/0.62         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.38/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.62  thf('36', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r1_tarski @ sk_A @ sk_B) | ((k3_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.62  thf('37', plain, ((((k1_xboole_0) = (sk_B)) | (r1_tarski @ sk_A @ sk_B))),
% 0.38/0.62      inference('sup+', [status(thm)], ['24', '36'])).
% 0.38/0.62  thf('38', plain, (((sk_B) != (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('39', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.38/0.62  thf('40', plain,
% 0.38/0.62      (![X12 : $i, X13 : $i]:
% 0.38/0.62         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.38/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.62  thf('41', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.62  thf('42', plain, (((sk_B) = (sk_A))),
% 0.38/0.62      inference('sup+', [status(thm)], ['23', '41'])).
% 0.38/0.62  thf('43', plain, (((sk_A) != (sk_B))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('44', plain, ($false),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
