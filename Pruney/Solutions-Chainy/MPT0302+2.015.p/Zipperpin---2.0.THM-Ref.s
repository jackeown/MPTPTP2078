%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cdn6PBFBJM

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:07 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   57 (  79 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  401 ( 657 expanded)
%              Number of equality atoms :   29 (  67 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X16 != X18 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X17 @ ( k1_tarski @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ~ ( r2_hidden @ X18 @ ( k4_xboole_0 @ X17 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X15 ) )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C_1 @ X2 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( k1_xboole_0 = X2 ) ) ),
    inference('sup-',[status(thm)],['0','8'])).

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

thf('10',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_B )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X15 ) )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( k1_xboole_0 = sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['22','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cdn6PBFBJM
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:08:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.35/1.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.35/1.53  % Solved by: fo/fo7.sh
% 1.35/1.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.35/1.53  % done 1027 iterations in 1.074s
% 1.35/1.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.35/1.53  % SZS output start Refutation
% 1.35/1.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.35/1.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.35/1.53  thf(sk_B_type, type, sk_B: $i).
% 1.35/1.53  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.35/1.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.35/1.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.35/1.53  thf(sk_A_type, type, sk_A: $i).
% 1.35/1.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.35/1.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.35/1.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.35/1.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.35/1.53  thf(d3_tarski, axiom,
% 1.35/1.53    (![A:$i,B:$i]:
% 1.35/1.53     ( ( r1_tarski @ A @ B ) <=>
% 1.35/1.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.35/1.53  thf('0', plain,
% 1.35/1.53      (![X1 : $i, X3 : $i]:
% 1.35/1.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.35/1.53      inference('cnf', [status(esa)], [d3_tarski])).
% 1.35/1.53  thf(t2_tarski, axiom,
% 1.35/1.53    (![A:$i,B:$i]:
% 1.35/1.53     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 1.35/1.53       ( ( A ) = ( B ) ) ))).
% 1.35/1.53  thf('1', plain,
% 1.35/1.53      (![X4 : $i, X5 : $i]:
% 1.35/1.53         (((X5) = (X4))
% 1.35/1.53          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 1.35/1.53          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 1.35/1.53      inference('cnf', [status(esa)], [t2_tarski])).
% 1.35/1.53  thf(t4_boole, axiom,
% 1.35/1.53    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.35/1.53  thf('2', plain,
% 1.35/1.53      (![X9 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 1.35/1.53      inference('cnf', [status(esa)], [t4_boole])).
% 1.35/1.53  thf(t64_zfmisc_1, axiom,
% 1.35/1.53    (![A:$i,B:$i,C:$i]:
% 1.35/1.53     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 1.35/1.53       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 1.35/1.53  thf('3', plain,
% 1.35/1.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.35/1.53         (((X16) != (X18))
% 1.35/1.53          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X17 @ (k1_tarski @ X18))))),
% 1.35/1.53      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 1.35/1.53  thf('4', plain,
% 1.35/1.53      (![X17 : $i, X18 : $i]:
% 1.35/1.53         ~ (r2_hidden @ X18 @ (k4_xboole_0 @ X17 @ (k1_tarski @ X18)))),
% 1.35/1.53      inference('simplify', [status(thm)], ['3'])).
% 1.35/1.53  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.35/1.53      inference('sup-', [status(thm)], ['2', '4'])).
% 1.35/1.53  thf('6', plain,
% 1.35/1.53      (![X0 : $i]:
% 1.35/1.53         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 1.35/1.53          | ((k1_xboole_0) = (X0)))),
% 1.35/1.53      inference('sup-', [status(thm)], ['1', '5'])).
% 1.35/1.53  thf(l54_zfmisc_1, axiom,
% 1.35/1.53    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.53     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 1.35/1.53       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 1.35/1.53  thf('7', plain,
% 1.35/1.53      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 1.35/1.53         ((r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X15))
% 1.35/1.53          | ~ (r2_hidden @ X13 @ X15)
% 1.35/1.53          | ~ (r2_hidden @ X11 @ X12))),
% 1.35/1.53      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.35/1.53  thf('8', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.53         (((k1_xboole_0) = (X0))
% 1.35/1.53          | ~ (r2_hidden @ X2 @ X1)
% 1.35/1.53          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_1 @ X0 @ k1_xboole_0)) @ 
% 1.35/1.53             (k2_zfmisc_1 @ X1 @ X0)))),
% 1.35/1.53      inference('sup-', [status(thm)], ['6', '7'])).
% 1.35/1.53  thf('9', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.53         ((r1_tarski @ X0 @ X1)
% 1.35/1.53          | (r2_hidden @ 
% 1.35/1.53             (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C_1 @ X2 @ k1_xboole_0)) @ 
% 1.35/1.53             (k2_zfmisc_1 @ X0 @ X2))
% 1.35/1.53          | ((k1_xboole_0) = (X2)))),
% 1.35/1.53      inference('sup-', [status(thm)], ['0', '8'])).
% 1.35/1.53  thf(t114_zfmisc_1, conjecture,
% 1.35/1.53    (![A:$i,B:$i]:
% 1.35/1.53     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 1.35/1.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.35/1.53         ( ( A ) = ( B ) ) ) ))).
% 1.35/1.53  thf(zf_stmt_0, negated_conjecture,
% 1.35/1.53    (~( ![A:$i,B:$i]:
% 1.35/1.53        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 1.35/1.53          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.35/1.53            ( ( A ) = ( B ) ) ) ) )),
% 1.35/1.53    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 1.35/1.53  thf('10', plain,
% 1.35/1.53      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf('11', plain,
% 1.35/1.53      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.35/1.53         ((r2_hidden @ X11 @ X12)
% 1.35/1.53          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 1.35/1.53      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.35/1.53  thf('12', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i]:
% 1.35/1.53         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.35/1.53          | (r2_hidden @ X1 @ sk_B))),
% 1.35/1.53      inference('sup-', [status(thm)], ['10', '11'])).
% 1.35/1.53  thf('13', plain,
% 1.35/1.53      (![X0 : $i]:
% 1.35/1.53         (((k1_xboole_0) = (sk_B))
% 1.35/1.53          | (r1_tarski @ sk_A @ X0)
% 1.35/1.53          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 1.35/1.53      inference('sup-', [status(thm)], ['9', '12'])).
% 1.35/1.53  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf('15', plain,
% 1.35/1.53      (![X0 : $i]:
% 1.35/1.53         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 1.35/1.53      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 1.35/1.53  thf('16', plain,
% 1.35/1.53      (![X1 : $i, X3 : $i]:
% 1.35/1.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.35/1.53      inference('cnf', [status(esa)], [d3_tarski])).
% 1.35/1.53  thf('17', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 1.35/1.53      inference('sup-', [status(thm)], ['15', '16'])).
% 1.35/1.53  thf('18', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.35/1.53      inference('simplify', [status(thm)], ['17'])).
% 1.35/1.53  thf(d10_xboole_0, axiom,
% 1.35/1.53    (![A:$i,B:$i]:
% 1.35/1.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.35/1.53  thf('19', plain,
% 1.35/1.53      (![X6 : $i, X8 : $i]:
% 1.35/1.53         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.35/1.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.35/1.53  thf('20', plain, ((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 1.35/1.53      inference('sup-', [status(thm)], ['18', '19'])).
% 1.35/1.53  thf('21', plain, (((sk_A) != (sk_B))),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf('22', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 1.35/1.53      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 1.35/1.53  thf('23', plain,
% 1.35/1.53      (![X0 : $i]:
% 1.35/1.53         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 1.35/1.53          | ((k1_xboole_0) = (X0)))),
% 1.35/1.53      inference('sup-', [status(thm)], ['1', '5'])).
% 1.35/1.53  thf('24', plain,
% 1.35/1.53      (![X1 : $i, X3 : $i]:
% 1.35/1.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.35/1.53      inference('cnf', [status(esa)], [d3_tarski])).
% 1.35/1.53  thf('25', plain,
% 1.35/1.53      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 1.35/1.53         ((r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X15))
% 1.35/1.53          | ~ (r2_hidden @ X13 @ X15)
% 1.35/1.53          | ~ (r2_hidden @ X11 @ X12))),
% 1.35/1.53      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.35/1.53  thf('26', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.35/1.53         ((r1_tarski @ X0 @ X1)
% 1.35/1.53          | ~ (r2_hidden @ X3 @ X2)
% 1.35/1.53          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 1.35/1.53             (k2_zfmisc_1 @ X2 @ X0)))),
% 1.35/1.53      inference('sup-', [status(thm)], ['24', '25'])).
% 1.35/1.53  thf('27', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.53         (((k1_xboole_0) = (X0))
% 1.35/1.53          | (r2_hidden @ 
% 1.35/1.53             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ (sk_C @ X2 @ X1)) @ 
% 1.35/1.53             (k2_zfmisc_1 @ X0 @ X1))
% 1.35/1.53          | (r1_tarski @ X1 @ X2))),
% 1.35/1.53      inference('sup-', [status(thm)], ['23', '26'])).
% 1.35/1.53  thf('28', plain,
% 1.35/1.53      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf('29', plain,
% 1.35/1.53      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.35/1.53         ((r2_hidden @ X13 @ X14)
% 1.35/1.53          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 1.35/1.53      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.35/1.53  thf('30', plain,
% 1.35/1.53      (![X0 : $i, X1 : $i]:
% 1.35/1.53         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.35/1.53          | (r2_hidden @ X0 @ sk_A))),
% 1.35/1.53      inference('sup-', [status(thm)], ['28', '29'])).
% 1.35/1.53  thf('31', plain,
% 1.35/1.53      (![X0 : $i]:
% 1.35/1.53         ((r1_tarski @ sk_B @ X0)
% 1.35/1.53          | ((k1_xboole_0) = (sk_A))
% 1.35/1.53          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 1.35/1.53      inference('sup-', [status(thm)], ['27', '30'])).
% 1.35/1.53  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 1.35/1.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.53  thf('33', plain,
% 1.35/1.53      (![X0 : $i]:
% 1.35/1.53         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 1.35/1.53      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 1.35/1.53  thf('34', plain,
% 1.35/1.53      (![X1 : $i, X3 : $i]:
% 1.35/1.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.35/1.53      inference('cnf', [status(esa)], [d3_tarski])).
% 1.35/1.53  thf('35', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 1.35/1.53      inference('sup-', [status(thm)], ['33', '34'])).
% 1.35/1.53  thf('36', plain, ((r1_tarski @ sk_B @ sk_A)),
% 1.35/1.53      inference('simplify', [status(thm)], ['35'])).
% 1.35/1.53  thf('37', plain, ($false), inference('demod', [status(thm)], ['22', '36'])).
% 1.35/1.53  
% 1.35/1.53  % SZS output end Refutation
% 1.35/1.53  
% 1.37/1.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
