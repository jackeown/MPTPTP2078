%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F1HMQY3xNM

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:25 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   54 (  71 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  327 ( 495 expanded)
%              Number of equality atoms :   30 (  33 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(t2_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
         => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v1_xboole_0 @ A )
          & ( v1_zfmisc_1 @ A ) )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
           => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_tex_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( v1_zfmisc_1 @ X19 )
      | ( X20 = X19 )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ( X10 = X11 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_xboole_0 @ X2 @ X1 )
        = X2 )
      | ~ ( v1_zfmisc_1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X2 @ X1 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_zfmisc_1 @ X2 )
      | ( ( k4_xboole_0 @ X2 @ X1 )
        = X2 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('10',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X2 @ X1 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_zfmisc_1 @ X2 )
      | ( ( k4_xboole_0 @ X2 @ X1 )
        = X2 ) ) ),
    inference('simplify_reflect+',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(clc,[status(thm)],['14','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( v1_zfmisc_1 @ X19 )
      | ( X20 = X19 )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['18','22','33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F1HMQY3xNM
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.00/1.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.00/1.20  % Solved by: fo/fo7.sh
% 1.00/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.20  % done 876 iterations in 0.752s
% 1.00/1.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.00/1.20  % SZS output start Refutation
% 1.00/1.20  thf(sk_B_type, type, sk_B: $i).
% 1.00/1.20  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.00/1.20  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.00/1.20  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.00/1.20  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.00/1.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.00/1.20  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 1.00/1.20  thf(t2_tex_2, conjecture,
% 1.00/1.20    (![A:$i]:
% 1.00/1.20     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 1.00/1.20       ( ![B:$i]:
% 1.00/1.20         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 1.00/1.20           ( r1_tarski @ A @ B ) ) ) ))).
% 1.00/1.20  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.20    (~( ![A:$i]:
% 1.00/1.20        ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 1.00/1.20          ( ![B:$i]:
% 1.00/1.20            ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 1.00/1.20              ( r1_tarski @ A @ B ) ) ) ) )),
% 1.00/1.20    inference('cnf.neg', [status(esa)], [t2_tex_2])).
% 1.00/1.20  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf(t36_xboole_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.00/1.20  thf('1', plain,
% 1.00/1.20      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 1.00/1.20      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.00/1.20  thf(t1_tex_2, axiom,
% 1.00/1.20    (![A:$i]:
% 1.00/1.20     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.00/1.20       ( ![B:$i]:
% 1.00/1.20         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 1.00/1.20           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 1.00/1.20  thf('2', plain,
% 1.00/1.20      (![X19 : $i, X20 : $i]:
% 1.00/1.20         ((v1_xboole_0 @ X19)
% 1.00/1.20          | ~ (v1_zfmisc_1 @ X19)
% 1.00/1.20          | ((X20) = (X19))
% 1.00/1.20          | ~ (r1_tarski @ X20 @ X19)
% 1.00/1.20          | (v1_xboole_0 @ X20))),
% 1.00/1.20      inference('cnf', [status(esa)], [t1_tex_2])).
% 1.00/1.20  thf('3', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((v1_xboole_0 @ (k4_xboole_0 @ X0 @ X1))
% 1.00/1.20          | ((k4_xboole_0 @ X0 @ X1) = (X0))
% 1.00/1.20          | ~ (v1_zfmisc_1 @ X0)
% 1.00/1.20          | (v1_xboole_0 @ X0))),
% 1.00/1.20      inference('sup-', [status(thm)], ['1', '2'])).
% 1.00/1.20  thf(t8_boole, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.00/1.20  thf('4', plain,
% 1.00/1.20      (![X10 : $i, X11 : $i]:
% 1.00/1.20         (~ (v1_xboole_0 @ X10) | ~ (v1_xboole_0 @ X11) | ((X10) = (X11)))),
% 1.00/1.20      inference('cnf', [status(esa)], [t8_boole])).
% 1.00/1.20  thf('5', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.20         ((v1_xboole_0 @ X1)
% 1.00/1.20          | ~ (v1_zfmisc_1 @ X1)
% 1.00/1.20          | ((k4_xboole_0 @ X1 @ X0) = (X1))
% 1.00/1.20          | ((k4_xboole_0 @ X1 @ X0) = (X2))
% 1.00/1.20          | ~ (v1_xboole_0 @ X2))),
% 1.00/1.20      inference('sup-', [status(thm)], ['3', '4'])).
% 1.00/1.20  thf(l32_xboole_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.00/1.20  thf('6', plain,
% 1.00/1.20      (![X3 : $i, X4 : $i]:
% 1.00/1.20         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 1.00/1.20      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.00/1.20  thf('7', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.20         (((X0) != (k1_xboole_0))
% 1.00/1.20          | ~ (v1_xboole_0 @ X0)
% 1.00/1.20          | ((k4_xboole_0 @ X2 @ X1) = (X2))
% 1.00/1.20          | ~ (v1_zfmisc_1 @ X2)
% 1.00/1.20          | (v1_xboole_0 @ X2)
% 1.00/1.20          | (r1_tarski @ X2 @ X1))),
% 1.00/1.20      inference('sup-', [status(thm)], ['5', '6'])).
% 1.00/1.20  thf('8', plain,
% 1.00/1.20      (![X1 : $i, X2 : $i]:
% 1.00/1.20         ((r1_tarski @ X2 @ X1)
% 1.00/1.20          | (v1_xboole_0 @ X2)
% 1.00/1.20          | ~ (v1_zfmisc_1 @ X2)
% 1.00/1.20          | ((k4_xboole_0 @ X2 @ X1) = (X2))
% 1.00/1.20          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.00/1.20      inference('simplify', [status(thm)], ['7'])).
% 1.00/1.20  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.00/1.20  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.00/1.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.00/1.20  thf('10', plain,
% 1.00/1.20      (![X1 : $i, X2 : $i]:
% 1.00/1.20         ((r1_tarski @ X2 @ X1)
% 1.00/1.20          | (v1_xboole_0 @ X2)
% 1.00/1.20          | ~ (v1_zfmisc_1 @ X2)
% 1.00/1.20          | ((k4_xboole_0 @ X2 @ X1) = (X2)))),
% 1.00/1.20      inference('simplify_reflect+', [status(thm)], ['8', '9'])).
% 1.00/1.20  thf('11', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('12', plain,
% 1.00/1.20      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))
% 1.00/1.20        | ~ (v1_zfmisc_1 @ sk_A)
% 1.00/1.20        | (v1_xboole_0 @ sk_A))),
% 1.00/1.20      inference('sup-', [status(thm)], ['10', '11'])).
% 1.00/1.20  thf('13', plain, ((v1_zfmisc_1 @ sk_A)),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('14', plain,
% 1.00/1.20      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)) | (v1_xboole_0 @ sk_A))),
% 1.00/1.20      inference('demod', [status(thm)], ['12', '13'])).
% 1.00/1.20  thf('15', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('16', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 1.00/1.20      inference('clc', [status(thm)], ['14', '15'])).
% 1.00/1.20  thf(t48_xboole_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.00/1.20  thf('17', plain,
% 1.00/1.20      (![X8 : $i, X9 : $i]:
% 1.00/1.20         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.00/1.20           = (k3_xboole_0 @ X8 @ X9))),
% 1.00/1.20      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.20  thf('18', plain,
% 1.00/1.20      (((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 1.00/1.20      inference('sup+', [status(thm)], ['16', '17'])).
% 1.00/1.20  thf(d10_xboole_0, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.00/1.20  thf('19', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.00/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.00/1.20  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.00/1.20      inference('simplify', [status(thm)], ['19'])).
% 1.00/1.20  thf('21', plain,
% 1.00/1.20      (![X3 : $i, X5 : $i]:
% 1.00/1.20         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 1.00/1.20      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.00/1.20  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.00/1.20      inference('sup-', [status(thm)], ['20', '21'])).
% 1.00/1.20  thf('23', plain,
% 1.00/1.20      (![X8 : $i, X9 : $i]:
% 1.00/1.20         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.00/1.20           = (k3_xboole_0 @ X8 @ X9))),
% 1.00/1.20      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.20  thf('24', plain,
% 1.00/1.20      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 1.00/1.20      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.00/1.20  thf('25', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.00/1.20      inference('sup+', [status(thm)], ['23', '24'])).
% 1.00/1.20  thf('26', plain,
% 1.00/1.20      (![X19 : $i, X20 : $i]:
% 1.00/1.20         ((v1_xboole_0 @ X19)
% 1.00/1.20          | ~ (v1_zfmisc_1 @ X19)
% 1.00/1.20          | ((X20) = (X19))
% 1.00/1.20          | ~ (r1_tarski @ X20 @ X19)
% 1.00/1.20          | (v1_xboole_0 @ X20))),
% 1.00/1.20      inference('cnf', [status(esa)], [t1_tex_2])).
% 1.00/1.20  thf('27', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((v1_xboole_0 @ (k3_xboole_0 @ X0 @ X1))
% 1.00/1.20          | ((k3_xboole_0 @ X0 @ X1) = (X0))
% 1.00/1.20          | ~ (v1_zfmisc_1 @ X0)
% 1.00/1.20          | (v1_xboole_0 @ X0))),
% 1.00/1.20      inference('sup-', [status(thm)], ['25', '26'])).
% 1.00/1.20  thf('28', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('29', plain,
% 1.00/1.20      (((v1_xboole_0 @ sk_A)
% 1.00/1.20        | ~ (v1_zfmisc_1 @ sk_A)
% 1.00/1.20        | ((k3_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['27', '28'])).
% 1.00/1.20  thf('30', plain, ((v1_zfmisc_1 @ sk_A)),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('31', plain,
% 1.00/1.20      (((v1_xboole_0 @ sk_A) | ((k3_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 1.00/1.20      inference('demod', [status(thm)], ['29', '30'])).
% 1.00/1.20  thf('32', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('33', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 1.00/1.20      inference('clc', [status(thm)], ['31', '32'])).
% 1.00/1.20  thf('34', plain, (((k1_xboole_0) = (sk_A))),
% 1.00/1.20      inference('demod', [status(thm)], ['18', '22', '33'])).
% 1.00/1.20  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.00/1.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.00/1.20  thf('36', plain, ($false),
% 1.00/1.20      inference('demod', [status(thm)], ['0', '34', '35'])).
% 1.00/1.20  
% 1.00/1.20  % SZS output end Refutation
% 1.00/1.20  
% 1.00/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
