%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BoJ9Bpn7A3

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:30 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   43 (  58 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  295 ( 467 expanded)
%              Number of equality atoms :   32 (  61 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('0',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('4',plain,(
    ! [X30: $i,X31: $i,X32: $i,X34: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X31 @ X32 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X30 ) @ X34 ) )
      | ~ ( r2_hidden @ X32 @ X34 )
      | ( X31 != X30 ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('5',plain,(
    ! [X30: $i,X32: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ X34 )
      | ( r2_hidden @ ( k4_tarski @ X30 @ X32 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X30 ) @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_B_1 @ ( sk_B @ sk_A ) ) @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_1 @ ( sk_B @ sk_A ) ) @ k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('11',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X40 @ X41 ) @ X42 )
      | ~ ( r2_hidden @ X40 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('12',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('18',plain,(
    ! [X35: $i,X36: $i,X37: $i,X39: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X35 @ X37 ) @ ( k2_zfmisc_1 @ X36 @ ( k1_tarski @ X39 ) ) )
      | ( X37 != X39 )
      | ~ ( r2_hidden @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('19',plain,(
    ! [X35: $i,X36: $i,X39: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ( r2_hidden @ ( k4_tarski @ X35 @ X39 ) @ ( k2_zfmisc_1 @ X36 @ ( k1_tarski @ X39 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ X1 ) @ ( k2_zfmisc_1 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ sk_B_1 ) @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','20'])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ sk_B_1 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('25',plain,(
    $false ),
    inference('sup-',[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BoJ9Bpn7A3
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 145 iterations in 0.075s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(t130_zfmisc_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.37/0.55       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.55         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i]:
% 0.37/0.55        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.37/0.55          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.55            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))
% 0.37/0.55        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))
% 0.37/0.55         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0)))
% 0.37/0.55         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf(t7_xboole_0, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.55          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.55  thf(t128_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.55     ( ( r2_hidden @
% 0.37/0.55         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.37/0.55       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (![X30 : $i, X31 : $i, X32 : $i, X34 : $i]:
% 0.37/0.55         ((r2_hidden @ (k4_tarski @ X31 @ X32) @ 
% 0.37/0.55           (k2_zfmisc_1 @ (k1_tarski @ X30) @ X34))
% 0.37/0.55          | ~ (r2_hidden @ X32 @ X34)
% 0.37/0.55          | ((X31) != (X30)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X30 : $i, X32 : $i, X34 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X32 @ X34)
% 0.37/0.55          | (r2_hidden @ (k4_tarski @ X30 @ X32) @ 
% 0.37/0.55             (k2_zfmisc_1 @ (k1_tarski @ X30) @ X34)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['4'])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (((X0) = (k1_xboole_0))
% 0.37/0.55          | (r2_hidden @ (k4_tarski @ X1 @ (sk_B @ X0)) @ 
% 0.37/0.55             (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['3', '5'])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      ((((r2_hidden @ (k4_tarski @ sk_B_1 @ (sk_B @ sk_A)) @ k1_xboole_0)
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.37/0.55         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))))),
% 0.37/0.55      inference('sup+', [status(thm)], ['2', '6'])).
% 0.37/0.55  thf('8', plain, (((sk_A) != (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (((r2_hidden @ (k4_tarski @ sk_B_1 @ (sk_B @ sk_A)) @ k1_xboole_0))
% 0.37/0.55         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))))),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.37/0.55  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.37/0.55  thf('10', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.55  thf(t55_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.37/0.55  thf('11', plain,
% 0.37/0.56      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.37/0.56         (~ (r1_xboole_0 @ (k2_tarski @ X40 @ X41) @ X42)
% 0.37/0.56          | ~ (r2_hidden @ X40 @ X42))),
% 0.37/0.56      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.37/0.56  thf('12', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.37/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['9', '12'])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))) | 
% 0.37/0.56       (((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))),
% 0.37/0.56      inference('sat_resolution*', [status(thm)], ['13', '14'])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))),
% 0.37/0.56      inference('simpl_trail', [status(thm)], ['1', '15'])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.37/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.56  thf(t129_zfmisc_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.56     ( ( r2_hidden @
% 0.37/0.56         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.37/0.56       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X35 : $i, X36 : $i, X37 : $i, X39 : $i]:
% 0.37/0.56         ((r2_hidden @ (k4_tarski @ X35 @ X37) @ 
% 0.37/0.56           (k2_zfmisc_1 @ X36 @ (k1_tarski @ X39)))
% 0.37/0.56          | ((X37) != (X39))
% 0.37/0.56          | ~ (r2_hidden @ X35 @ X36))),
% 0.37/0.56      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X35 : $i, X36 : $i, X39 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X35 @ X36)
% 0.37/0.56          | (r2_hidden @ (k4_tarski @ X35 @ X39) @ 
% 0.37/0.56             (k2_zfmisc_1 @ X36 @ (k1_tarski @ X39))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((X0) = (k1_xboole_0))
% 0.37/0.56          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ X1) @ 
% 0.37/0.56             (k2_zfmisc_1 @ X0 @ (k1_tarski @ X1))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['17', '19'])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ sk_B_1) @ k1_xboole_0)
% 0.37/0.56        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['16', '20'])).
% 0.37/0.56  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      ((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ sk_B_1) @ k1_xboole_0)),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.37/0.56  thf('24', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.37/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.56  thf('25', plain, ($false), inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
