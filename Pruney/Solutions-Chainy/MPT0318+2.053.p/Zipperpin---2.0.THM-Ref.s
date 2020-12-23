%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wn5iZ2jD2Z

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:28 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   55 (  80 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  364 ( 605 expanded)
%              Number of equality atoms :   44 (  85 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X35: $i,X36: $i,X37: $i,X39: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X36 @ X37 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X35 ) @ X39 ) )
      | ~ ( r2_hidden @ X37 @ X39 )
      | ( X36 != X35 ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('5',plain,(
    ! [X35: $i,X37: $i,X39: $i] :
      ( ~ ( r2_hidden @ X37 @ X39 )
      | ( r2_hidden @ ( k4_tarski @ X35 @ X37 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X35 ) @ X39 ) ) ) ),
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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ( ( k4_xboole_0 @ X46 @ ( k1_tarski @ X45 ) )
       != X46 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('25',plain,(
    ! [X40: $i,X41: $i,X42: $i,X44: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X40 @ X42 ) @ ( k2_zfmisc_1 @ X41 @ ( k1_tarski @ X44 ) ) )
      | ( X42 != X44 )
      | ~ ( r2_hidden @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('26',plain,(
    ! [X40: $i,X41: $i,X44: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( r2_hidden @ ( k4_tarski @ X40 @ X44 ) @ ( k2_zfmisc_1 @ X41 @ ( k1_tarski @ X44 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ X1 ) @ ( k2_zfmisc_1 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ sk_B_1 ) @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','27'])).

thf('29',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ sk_B_1 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('32',plain,(
    $false ),
    inference('sup-',[status(thm)],['30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wn5iZ2jD2Z
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:41:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 164 iterations in 0.068s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.35/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.53  thf(t130_zfmisc_1, conjecture,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.35/0.53       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.53         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i,B:$i]:
% 0.35/0.53        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.35/0.53          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.53            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.35/0.53  thf('0', plain,
% 0.35/0.53      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))
% 0.35/0.53        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))))),
% 0.35/0.53      inference('split', [status(esa)], ['0'])).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0)))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('split', [status(esa)], ['0'])).
% 0.35/0.53  thf(t7_xboole_0, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.35/0.53  thf('3', plain,
% 0.35/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.35/0.53  thf(t128_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.53     ( ( r2_hidden @
% 0.35/0.53         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.35/0.53       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      (![X35 : $i, X36 : $i, X37 : $i, X39 : $i]:
% 0.35/0.53         ((r2_hidden @ (k4_tarski @ X36 @ X37) @ 
% 0.35/0.53           (k2_zfmisc_1 @ (k1_tarski @ X35) @ X39))
% 0.35/0.53          | ~ (r2_hidden @ X37 @ X39)
% 0.35/0.53          | ((X36) != (X35)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.35/0.53  thf('5', plain,
% 0.35/0.53      (![X35 : $i, X37 : $i, X39 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X37 @ X39)
% 0.35/0.53          | (r2_hidden @ (k4_tarski @ X35 @ X37) @ 
% 0.35/0.53             (k2_zfmisc_1 @ (k1_tarski @ X35) @ X39)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((X0) = (k1_xboole_0))
% 0.35/0.53          | (r2_hidden @ (k4_tarski @ X1 @ (sk_B @ X0)) @ 
% 0.35/0.53             (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['3', '5'])).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      ((((r2_hidden @ (k4_tarski @ sk_B_1 @ (sk_B @ sk_A)) @ k1_xboole_0)
% 0.35/0.53         | ((sk_A) = (k1_xboole_0))))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('sup+', [status(thm)], ['2', '6'])).
% 0.35/0.53  thf('8', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('9', plain,
% 0.35/0.53      (((r2_hidden @ (k4_tarski @ sk_B_1 @ (sk_B @ sk_A)) @ k1_xboole_0))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.35/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.35/0.53  thf('10', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.35/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.53  thf(t28_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.35/0.53  thf('11', plain,
% 0.35/0.53      (![X3 : $i, X4 : $i]:
% 0.35/0.53         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.35/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.35/0.53  thf('12', plain,
% 0.35/0.53      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.53  thf(t100_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      (![X1 : $i, X2 : $i]:
% 0.35/0.53         ((k4_xboole_0 @ X1 @ X2)
% 0.35/0.53           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.53  thf('14', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.35/0.53           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['12', '13'])).
% 0.35/0.53  thf(t92_xboole_1, axiom,
% 0.35/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.35/0.53  thf('15', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.53  thf('16', plain,
% 0.35/0.53      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.35/0.53  thf(t65_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.35/0.53       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (![X45 : $i, X46 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X45 @ X46)
% 0.35/0.53          | ((k4_xboole_0 @ X46 @ (k1_tarski @ X45)) != (X46)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.53  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.35/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.35/0.53  thf('20', plain,
% 0.35/0.53      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['9', '19'])).
% 0.35/0.53  thf('21', plain,
% 0.35/0.53      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))) | 
% 0.35/0.53       (((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0)))),
% 0.35/0.53      inference('split', [status(esa)], ['0'])).
% 0.35/0.53  thf('22', plain,
% 0.35/0.53      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))),
% 0.35/0.53      inference('sat_resolution*', [status(thm)], ['20', '21'])).
% 0.35/0.53  thf('23', plain,
% 0.35/0.53      (((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))),
% 0.35/0.53      inference('simpl_trail', [status(thm)], ['1', '22'])).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.35/0.53  thf(t129_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.53     ( ( r2_hidden @
% 0.35/0.53         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.35/0.53       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.35/0.53  thf('25', plain,
% 0.35/0.53      (![X40 : $i, X41 : $i, X42 : $i, X44 : $i]:
% 0.35/0.53         ((r2_hidden @ (k4_tarski @ X40 @ X42) @ 
% 0.35/0.53           (k2_zfmisc_1 @ X41 @ (k1_tarski @ X44)))
% 0.35/0.53          | ((X42) != (X44))
% 0.35/0.53          | ~ (r2_hidden @ X40 @ X41))),
% 0.35/0.53      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      (![X40 : $i, X41 : $i, X44 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X40 @ X41)
% 0.35/0.53          | (r2_hidden @ (k4_tarski @ X40 @ X44) @ 
% 0.35/0.53             (k2_zfmisc_1 @ X41 @ (k1_tarski @ X44))))),
% 0.35/0.53      inference('simplify', [status(thm)], ['25'])).
% 0.35/0.53  thf('27', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((X0) = (k1_xboole_0))
% 0.35/0.53          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ X1) @ 
% 0.35/0.53             (k2_zfmisc_1 @ X0 @ (k1_tarski @ X1))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['24', '26'])).
% 0.35/0.53  thf('28', plain,
% 0.35/0.53      (((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ sk_B_1) @ k1_xboole_0)
% 0.35/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['23', '27'])).
% 0.35/0.53  thf('29', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('30', plain,
% 0.35/0.53      ((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ sk_B_1) @ k1_xboole_0)),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.35/0.53  thf('31', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.35/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.35/0.53  thf('32', plain, ($false), inference('sup-', [status(thm)], ['30', '31'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.38/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
