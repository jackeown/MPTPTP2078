%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m9CSKCbSlh

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:24 EST 2020

% Result     : Theorem 0.95s
% Output     : Refutation 0.95s
% Verified   : 
% Statistics : Number of formulae       :   52 (  78 expanded)
%              Number of leaves         :   16 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  302 ( 507 expanded)
%              Number of equality atoms :   29 (  65 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t130_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != k1_xboole_0 )
       => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
           != k1_xboole_0 )
          & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_zfmisc_1])).

thf('1',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( sk_A_1 != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ~ ( v1_xboole_0 @ sk_A_1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('8',plain,(
    ! [X32: $i,X33: $i,X34: $i,X36: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X33 @ X34 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X32 ) @ X36 ) )
      | ~ ( r2_hidden @ X34 @ X36 )
      | ( X33 != X32 ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('9',plain,(
    ! [X32: $i,X34: $i,X36: $i] :
      ( ~ ( r2_hidden @ X34 @ X36 )
      | ( r2_hidden @ ( k4_tarski @ X32 @ X34 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X32 ) @ X36 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A_1 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('14',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('15',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('16',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('17',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ sk_A_1 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,(
    ~ ( v1_xboole_0 @ sk_A_1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('21',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('23',plain,
    ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['5','23'])).

thf('25',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('26',plain,(
    ! [X37: $i,X38: $i,X39: $i,X41: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X37 @ X39 ) @ ( k2_zfmisc_1 @ X38 @ ( k1_tarski @ X41 ) ) )
      | ( X39 != X41 )
      | ~ ( r2_hidden @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('27',plain,(
    ! [X37: $i,X38: $i,X41: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ( r2_hidden @ ( k4_tarski @ X37 @ X41 ) @ ( k2_zfmisc_1 @ X38 @ ( k1_tarski @ X41 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ X1 ) @ ( k2_zfmisc_1 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['14','17'])).

thf('33',plain,(
    v1_xboole_0 @ sk_A_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['3','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m9CSKCbSlh
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.95/1.15  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.95/1.15  % Solved by: fo/fo7.sh
% 0.95/1.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.95/1.15  % done 1026 iterations in 0.691s
% 0.95/1.15  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.95/1.15  % SZS output start Refutation
% 0.95/1.15  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.95/1.15  thf(sk_A_type, type, sk_A: $i).
% 0.95/1.15  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.95/1.15  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.95/1.15  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.95/1.15  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.95/1.15  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.95/1.15  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.95/1.15  thf(sk_B_type, type, sk_B: $i > $i).
% 0.95/1.15  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.95/1.15  thf(l13_xboole_0, axiom,
% 0.95/1.15    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.95/1.15  thf('0', plain,
% 0.95/1.15      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.95/1.15      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.95/1.15  thf(t130_zfmisc_1, conjecture,
% 0.95/1.15    (![A:$i,B:$i]:
% 0.95/1.15     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.95/1.15       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.95/1.15         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.95/1.15  thf(zf_stmt_0, negated_conjecture,
% 0.95/1.15    (~( ![A:$i,B:$i]:
% 0.95/1.15        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.95/1.15          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.95/1.15            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.95/1.15    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.95/1.15  thf('1', plain, (((sk_A_1) != (k1_xboole_0))),
% 0.95/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.15  thf('2', plain, (![X0 : $i]: (((sk_A_1) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.95/1.15      inference('sup-', [status(thm)], ['0', '1'])).
% 0.95/1.15  thf('3', plain, (~ (v1_xboole_0 @ sk_A_1)),
% 0.95/1.15      inference('simplify', [status(thm)], ['2'])).
% 0.95/1.15  thf('4', plain,
% 0.95/1.15      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0))
% 0.95/1.15        | ((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))),
% 0.95/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.95/1.15  thf('5', plain,
% 0.95/1.15      ((((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))
% 0.95/1.15         <= ((((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))))),
% 0.95/1.15      inference('split', [status(esa)], ['4'])).
% 0.95/1.15  thf('6', plain,
% 0.95/1.15      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0)))
% 0.95/1.15         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0))))),
% 0.95/1.15      inference('split', [status(esa)], ['4'])).
% 0.95/1.15  thf(d1_xboole_0, axiom,
% 0.95/1.15    (![A:$i]:
% 0.95/1.15     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.95/1.15  thf('7', plain,
% 0.95/1.15      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.95/1.15      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.95/1.15  thf(t128_zfmisc_1, axiom,
% 0.95/1.15    (![A:$i,B:$i,C:$i,D:$i]:
% 0.95/1.15     ( ( r2_hidden @
% 0.95/1.15         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.95/1.15       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.95/1.15  thf('8', plain,
% 0.95/1.15      (![X32 : $i, X33 : $i, X34 : $i, X36 : $i]:
% 0.95/1.15         ((r2_hidden @ (k4_tarski @ X33 @ X34) @ 
% 0.95/1.15           (k2_zfmisc_1 @ (k1_tarski @ X32) @ X36))
% 0.95/1.15          | ~ (r2_hidden @ X34 @ X36)
% 0.95/1.15          | ((X33) != (X32)))),
% 0.95/1.15      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.95/1.15  thf('9', plain,
% 0.95/1.15      (![X32 : $i, X34 : $i, X36 : $i]:
% 0.95/1.15         (~ (r2_hidden @ X34 @ X36)
% 0.95/1.15          | (r2_hidden @ (k4_tarski @ X32 @ X34) @ 
% 0.95/1.15             (k2_zfmisc_1 @ (k1_tarski @ X32) @ X36)))),
% 0.95/1.15      inference('simplify', [status(thm)], ['8'])).
% 0.95/1.15  thf('10', plain,
% 0.95/1.15      (![X0 : $i, X1 : $i]:
% 0.95/1.15         ((v1_xboole_0 @ X0)
% 0.95/1.15          | (r2_hidden @ (k4_tarski @ X1 @ (sk_B @ X0)) @ 
% 0.95/1.15             (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)))),
% 0.95/1.15      inference('sup-', [status(thm)], ['7', '9'])).
% 0.95/1.15  thf('11', plain,
% 0.95/1.15      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.95/1.15      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.95/1.15  thf('12', plain,
% 0.95/1.15      (![X0 : $i, X1 : $i]:
% 0.95/1.15         ((v1_xboole_0 @ X0)
% 0.95/1.15          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)))),
% 0.95/1.15      inference('sup-', [status(thm)], ['10', '11'])).
% 0.95/1.15  thf('13', plain,
% 0.95/1.15      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_A_1)))
% 0.95/1.15         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0))))),
% 0.95/1.15      inference('sup-', [status(thm)], ['6', '12'])).
% 0.95/1.15  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.95/1.15  thf('14', plain, ((v1_xboole_0 @ sk_A)),
% 0.95/1.15      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.95/1.15  thf('15', plain, ((v1_xboole_0 @ sk_A)),
% 0.95/1.15      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.95/1.15  thf('16', plain,
% 0.95/1.15      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.95/1.15      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.95/1.15  thf('17', plain, (((sk_A) = (k1_xboole_0))),
% 0.95/1.15      inference('sup-', [status(thm)], ['15', '16'])).
% 0.95/1.15  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.95/1.15      inference('demod', [status(thm)], ['14', '17'])).
% 0.95/1.15  thf('19', plain,
% 0.95/1.15      (((v1_xboole_0 @ sk_A_1))
% 0.95/1.15         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0))))),
% 0.95/1.15      inference('demod', [status(thm)], ['13', '18'])).
% 0.95/1.15  thf('20', plain, (~ (v1_xboole_0 @ sk_A_1)),
% 0.95/1.15      inference('simplify', [status(thm)], ['2'])).
% 0.95/1.15  thf('21', plain,
% 0.95/1.15      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0)))),
% 0.95/1.15      inference('sup-', [status(thm)], ['19', '20'])).
% 0.95/1.15  thf('22', plain,
% 0.95/1.15      ((((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))) | 
% 0.95/1.15       (((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0)))),
% 0.95/1.15      inference('split', [status(esa)], ['4'])).
% 0.95/1.15  thf('23', plain,
% 0.95/1.15      ((((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))),
% 0.95/1.15      inference('sat_resolution*', [status(thm)], ['21', '22'])).
% 0.95/1.15  thf('24', plain,
% 0.95/1.15      (((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))),
% 0.95/1.15      inference('simpl_trail', [status(thm)], ['5', '23'])).
% 0.95/1.15  thf('25', plain,
% 0.95/1.15      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.95/1.15      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.95/1.15  thf(t129_zfmisc_1, axiom,
% 0.95/1.15    (![A:$i,B:$i,C:$i,D:$i]:
% 0.95/1.15     ( ( r2_hidden @
% 0.95/1.15         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.95/1.15       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.95/1.15  thf('26', plain,
% 0.95/1.15      (![X37 : $i, X38 : $i, X39 : $i, X41 : $i]:
% 0.95/1.15         ((r2_hidden @ (k4_tarski @ X37 @ X39) @ 
% 0.95/1.15           (k2_zfmisc_1 @ X38 @ (k1_tarski @ X41)))
% 0.95/1.15          | ((X39) != (X41))
% 0.95/1.15          | ~ (r2_hidden @ X37 @ X38))),
% 0.95/1.15      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 0.95/1.15  thf('27', plain,
% 0.95/1.15      (![X37 : $i, X38 : $i, X41 : $i]:
% 0.95/1.15         (~ (r2_hidden @ X37 @ X38)
% 0.95/1.15          | (r2_hidden @ (k4_tarski @ X37 @ X41) @ 
% 0.95/1.15             (k2_zfmisc_1 @ X38 @ (k1_tarski @ X41))))),
% 0.95/1.15      inference('simplify', [status(thm)], ['26'])).
% 0.95/1.15  thf('28', plain,
% 0.95/1.15      (![X0 : $i, X1 : $i]:
% 0.95/1.15         ((v1_xboole_0 @ X0)
% 0.95/1.15          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ X1) @ 
% 0.95/1.15             (k2_zfmisc_1 @ X0 @ (k1_tarski @ X1))))),
% 0.95/1.15      inference('sup-', [status(thm)], ['25', '27'])).
% 0.95/1.15  thf('29', plain,
% 0.95/1.15      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.95/1.15      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.95/1.15  thf('30', plain,
% 0.95/1.15      (![X0 : $i, X1 : $i]:
% 0.95/1.15         ((v1_xboole_0 @ X1)
% 0.95/1.15          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.95/1.15      inference('sup-', [status(thm)], ['28', '29'])).
% 0.95/1.15  thf('31', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_A_1))),
% 0.95/1.15      inference('sup-', [status(thm)], ['24', '30'])).
% 0.95/1.15  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.95/1.15      inference('demod', [status(thm)], ['14', '17'])).
% 0.95/1.15  thf('33', plain, ((v1_xboole_0 @ sk_A_1)),
% 0.95/1.15      inference('demod', [status(thm)], ['31', '32'])).
% 0.95/1.15  thf('34', plain, ($false), inference('demod', [status(thm)], ['3', '33'])).
% 0.95/1.15  
% 0.95/1.15  % SZS output end Refutation
% 0.95/1.15  
% 0.95/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
