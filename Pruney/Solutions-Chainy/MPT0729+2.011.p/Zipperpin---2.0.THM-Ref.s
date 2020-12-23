%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nZ4mJAiRkb

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 110 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  279 ( 752 expanded)
%              Number of equality atoms :   25 (  84 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('0',plain,(
    ! [X17: $i] :
      ( ( k1_ordinal1 @ X17 )
      = ( k2_xboole_0 @ X17 @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t141_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ ( k1_tarski @ X12 ) ) @ ( k1_tarski @ X12 ) )
        = X11 )
      | ( r2_hidden @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t141_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_ordinal1 @ X0 ) @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r2_hidden @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t12_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k1_ordinal1 @ A )
        = ( k1_ordinal1 @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k1_ordinal1 @ A )
          = ( k1_ordinal1 @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_ordinal1])).

thf('3',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('4',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('5',plain,(
    r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k4_xboole_0 @ X14 @ ( k1_tarski @ X16 ) ) )
      | ( X13 = X16 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ~ ( r2_hidden @ ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ ( k1_tarski @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_ordinal1 @ X0 ) @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r2_hidden @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = sk_B )
    | ( r2_hidden @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('17',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k4_xboole_0 @ X14 @ ( k1_tarski @ X16 ) ) )
      | ( X13 = X16 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_ordinal1 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_B @ sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_B @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('23',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_tarski @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['23','25'])).

thf('27',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['12','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('29',plain,(
    ~ ( r2_hidden @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['12','26'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['29','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nZ4mJAiRkb
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 64 iterations in 0.030s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(d1_ordinal1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X17 : $i]:
% 0.20/0.48         ((k1_ordinal1 @ X17) = (k2_xboole_0 @ X17 @ (k1_tarski @ X17)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.20/0.48  thf(t141_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ~( r2_hidden @ A @ B ) ) =>
% 0.20/0.48       ( ( k4_xboole_0 @
% 0.20/0.48           ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.20/0.48         ( B ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (((k4_xboole_0 @ (k2_xboole_0 @ X11 @ (k1_tarski @ X12)) @ 
% 0.20/0.48            (k1_tarski @ X12)) = (X11))
% 0.20/0.48          | (r2_hidden @ X12 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t141_zfmisc_1])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k4_xboole_0 @ (k1_ordinal1 @ X0) @ (k1_tarski @ X0)) = (X0))
% 0.20/0.48          | (r2_hidden @ X0 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf(t12_ordinal1, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t12_ordinal1])).
% 0.20/0.48  thf('3', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.20/0.48  thf('4', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_ordinal1 @ X18))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.20/0.48  thf('5', plain, ((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))),
% 0.20/0.48      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf(t64_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.20/0.48       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.20/0.48         ((r2_hidden @ X13 @ (k4_xboole_0 @ X14 @ (k1_tarski @ X16)))
% 0.20/0.48          | ((X13) = (X16))
% 0.20/0.48          | ~ (r2_hidden @ X13 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((sk_B) = (X0))
% 0.20/0.48          | (r2_hidden @ sk_B @ 
% 0.20/0.48             (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ (k1_tarski @ X0))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf(antisymmetry_r2_hidden, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((sk_B) = (X0))
% 0.20/0.48          | ~ (r2_hidden @ 
% 0.20/0.48               (k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ (k1_tarski @ X0)) @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.20/0.48        | (r2_hidden @ sk_A @ sk_A)
% 0.20/0.48        | ((sk_B) = (sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '9'])).
% 0.20/0.48  thf('11', plain, (((sk_A) != (sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('12', plain, ((~ (r2_hidden @ sk_A @ sk_B) | (r2_hidden @ sk_A @ sk_A))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k4_xboole_0 @ (k1_ordinal1 @ X0) @ (k1_tarski @ X0)) = (X0))
% 0.20/0.48          | (r2_hidden @ X0 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((((k4_xboole_0 @ (k1_ordinal1 @ sk_A) @ (k1_tarski @ sk_B)) = (sk_B))
% 0.20/0.48        | (r2_hidden @ sk_B @ sk_B))),
% 0.20/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_ordinal1 @ X18))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.20/0.48         ((r2_hidden @ X13 @ (k4_xboole_0 @ X14 @ (k1_tarski @ X16)))
% 0.20/0.48          | ((X13) = (X16))
% 0.20/0.48          | ~ (r2_hidden @ X13 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) = (X1))
% 0.20/0.48          | (r2_hidden @ X0 @ 
% 0.20/0.48             (k4_xboole_0 @ (k1_ordinal1 @ X0) @ (k1_tarski @ X1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (((r2_hidden @ sk_A @ sk_B)
% 0.20/0.48        | (r2_hidden @ sk_B @ sk_B)
% 0.20/0.48        | ((sk_A) = (sk_B)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['15', '18'])).
% 0.20/0.48  thf('20', plain, (((sk_A) != (sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('21', plain, (((r2_hidden @ sk_A @ sk_B) | (r2_hidden @ sk_B @ sk_B))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf(t7_ordinal1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X19 : $i, X20 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.48  thf('23', plain, (((r2_hidden @ sk_A @ sk_B) | ~ (r1_tarski @ sk_B @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf(d10_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.48  thf('25', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.20/0.48      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.48  thf('26', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.48      inference('demod', [status(thm)], ['23', '25'])).
% 0.20/0.48  thf('27', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['12', '26'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.20/0.48  thf('29', plain, (~ (r2_hidden @ sk_A @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['12', '26'])).
% 0.20/0.48  thf('31', plain, ($false), inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
