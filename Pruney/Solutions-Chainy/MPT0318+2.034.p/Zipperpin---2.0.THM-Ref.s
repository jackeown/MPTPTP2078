%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B8SBusfsuN

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:25 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   51 (  85 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  390 ( 759 expanded)
%              Number of equality atoms :   42 (  91 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('4',plain,(
    ! [X39: $i,X40: $i,X41: $i,X43: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X40 @ X41 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X39 ) @ X43 ) )
      | ~ ( r2_hidden @ X41 @ X43 )
      | ( X40 != X39 ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('5',plain,(
    ! [X39: $i,X41: $i,X43: $i] :
      ( ~ ( r2_hidden @ X41 @ X43 )
      | ( r2_hidden @ ( k4_tarski @ X39 @ X41 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X39 ) @ X43 ) ) ) ),
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

thf('10',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['21'])).

thf('23',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','22'])).

thf('24',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','25'])).

thf('27',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('28',plain,(
    ! [X44: $i,X45: $i,X46: $i,X48: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X44 @ X46 ) @ ( k2_zfmisc_1 @ X45 @ ( k1_tarski @ X48 ) ) )
      | ( X46 != X48 )
      | ~ ( r2_hidden @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('29',plain,(
    ! [X44: $i,X45: $i,X48: $i] :
      ( ~ ( r2_hidden @ X44 @ X45 )
      | ( r2_hidden @ ( k4_tarski @ X44 @ X48 ) @ ( k2_zfmisc_1 @ X45 @ ( k1_tarski @ X48 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ X1 ) @ ( k2_zfmisc_1 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ sk_B_1 ) @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','30'])).

thf('32',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ sk_B_1 ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['21'])).

thf('35',plain,(
    $false ),
    inference('sup-',[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B8SBusfsuN
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:06:10 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.34/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.61  % Solved by: fo/fo7.sh
% 0.34/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.61  % done 278 iterations in 0.154s
% 0.34/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.61  % SZS output start Refutation
% 0.34/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.34/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.34/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.34/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.34/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.61  thf(t130_zfmisc_1, conjecture,
% 0.34/0.61    (![A:$i,B:$i]:
% 0.34/0.61     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.34/0.61       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.34/0.61         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.34/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.61    (~( ![A:$i,B:$i]:
% 0.34/0.61        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.34/0.61          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.34/0.61            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.34/0.61    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.34/0.61  thf('0', plain,
% 0.34/0.61      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))
% 0.34/0.61        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))),
% 0.34/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.61  thf('1', plain,
% 0.34/0.61      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))
% 0.34/0.61         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))))),
% 0.34/0.61      inference('split', [status(esa)], ['0'])).
% 0.34/0.61  thf('2', plain,
% 0.34/0.61      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0)))
% 0.34/0.61         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))))),
% 0.34/0.61      inference('split', [status(esa)], ['0'])).
% 0.34/0.61  thf(t7_xboole_0, axiom,
% 0.34/0.61    (![A:$i]:
% 0.34/0.61     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.34/0.61          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.34/0.61  thf('3', plain,
% 0.34/0.61      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.34/0.61      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.34/0.61  thf(t128_zfmisc_1, axiom,
% 0.34/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.61     ( ( r2_hidden @
% 0.34/0.61         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.34/0.61       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.34/0.61  thf('4', plain,
% 0.34/0.61      (![X39 : $i, X40 : $i, X41 : $i, X43 : $i]:
% 0.34/0.61         ((r2_hidden @ (k4_tarski @ X40 @ X41) @ 
% 0.34/0.61           (k2_zfmisc_1 @ (k1_tarski @ X39) @ X43))
% 0.34/0.61          | ~ (r2_hidden @ X41 @ X43)
% 0.34/0.61          | ((X40) != (X39)))),
% 0.34/0.61      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.34/0.61  thf('5', plain,
% 0.34/0.61      (![X39 : $i, X41 : $i, X43 : $i]:
% 0.34/0.61         (~ (r2_hidden @ X41 @ X43)
% 0.34/0.61          | (r2_hidden @ (k4_tarski @ X39 @ X41) @ 
% 0.34/0.61             (k2_zfmisc_1 @ (k1_tarski @ X39) @ X43)))),
% 0.34/0.61      inference('simplify', [status(thm)], ['4'])).
% 0.34/0.61  thf('6', plain,
% 0.34/0.61      (![X0 : $i, X1 : $i]:
% 0.34/0.61         (((X0) = (k1_xboole_0))
% 0.34/0.61          | (r2_hidden @ (k4_tarski @ X1 @ (sk_B @ X0)) @ 
% 0.34/0.61             (k2_zfmisc_1 @ (k1_tarski @ X1) @ X0)))),
% 0.34/0.61      inference('sup-', [status(thm)], ['3', '5'])).
% 0.34/0.61  thf('7', plain,
% 0.34/0.61      ((((r2_hidden @ (k4_tarski @ sk_B_1 @ (sk_B @ sk_A)) @ k1_xboole_0)
% 0.34/0.61         | ((sk_A) = (k1_xboole_0))))
% 0.34/0.61         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))))),
% 0.34/0.61      inference('sup+', [status(thm)], ['2', '6'])).
% 0.34/0.61  thf('8', plain, (((sk_A) != (k1_xboole_0))),
% 0.34/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.61  thf('9', plain,
% 0.34/0.61      (((r2_hidden @ (k4_tarski @ sk_B_1 @ (sk_B @ sk_A)) @ k1_xboole_0))
% 0.34/0.61         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0))))),
% 0.34/0.61      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.34/0.61  thf('10', plain,
% 0.34/0.61      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.34/0.61      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.34/0.61  thf(d5_xboole_0, axiom,
% 0.34/0.61    (![A:$i,B:$i,C:$i]:
% 0.34/0.61     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.34/0.61       ( ![D:$i]:
% 0.34/0.61         ( ( r2_hidden @ D @ C ) <=>
% 0.34/0.61           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.34/0.61  thf('11', plain,
% 0.34/0.61      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.34/0.61         (~ (r2_hidden @ X4 @ X3)
% 0.34/0.61          | (r2_hidden @ X4 @ X1)
% 0.34/0.61          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.34/0.61      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.34/0.61  thf('12', plain,
% 0.34/0.61      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.34/0.61         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.34/0.61      inference('simplify', [status(thm)], ['11'])).
% 0.34/0.61  thf('13', plain,
% 0.34/0.61      (![X0 : $i, X1 : $i]:
% 0.34/0.61         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.34/0.61          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.34/0.61      inference('sup-', [status(thm)], ['10', '12'])).
% 0.34/0.61  thf('14', plain,
% 0.34/0.61      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.34/0.61      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.34/0.61  thf('15', plain,
% 0.34/0.61      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.34/0.61         (~ (r2_hidden @ X4 @ X3)
% 0.34/0.61          | ~ (r2_hidden @ X4 @ X2)
% 0.34/0.61          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.34/0.61      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.34/0.61  thf('16', plain,
% 0.34/0.61      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.34/0.61         (~ (r2_hidden @ X4 @ X2)
% 0.34/0.61          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.34/0.61      inference('simplify', [status(thm)], ['15'])).
% 0.34/0.61  thf('17', plain,
% 0.34/0.61      (![X0 : $i, X1 : $i]:
% 0.34/0.61         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.34/0.61          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.34/0.61      inference('sup-', [status(thm)], ['14', '16'])).
% 0.34/0.61  thf('18', plain,
% 0.34/0.61      (![X0 : $i]:
% 0.34/0.61         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.34/0.61          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.34/0.61      inference('sup-', [status(thm)], ['13', '17'])).
% 0.34/0.61  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.34/0.61      inference('simplify', [status(thm)], ['18'])).
% 0.34/0.61  thf('20', plain,
% 0.34/0.61      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.34/0.61         (~ (r2_hidden @ X4 @ X2)
% 0.34/0.61          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.34/0.61      inference('simplify', [status(thm)], ['15'])).
% 0.34/0.61  thf('21', plain,
% 0.34/0.61      (![X0 : $i, X1 : $i]:
% 0.34/0.61         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.34/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.34/0.61  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.34/0.61      inference('condensation', [status(thm)], ['21'])).
% 0.34/0.61  thf('23', plain,
% 0.34/0.61      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0)))),
% 0.34/0.61      inference('sup-', [status(thm)], ['9', '22'])).
% 0.34/0.61  thf('24', plain,
% 0.34/0.61      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))) | 
% 0.34/0.61       (((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0)))),
% 0.34/0.61      inference('split', [status(esa)], ['0'])).
% 0.34/0.61  thf('25', plain,
% 0.34/0.61      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))),
% 0.34/0.61      inference('sat_resolution*', [status(thm)], ['23', '24'])).
% 0.34/0.61  thf('26', plain,
% 0.34/0.61      (((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))),
% 0.34/0.61      inference('simpl_trail', [status(thm)], ['1', '25'])).
% 0.34/0.61  thf('27', plain,
% 0.34/0.61      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.34/0.61      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.34/0.61  thf(t129_zfmisc_1, axiom,
% 0.34/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.61     ( ( r2_hidden @
% 0.34/0.61         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.34/0.61       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.34/0.61  thf('28', plain,
% 0.34/0.61      (![X44 : $i, X45 : $i, X46 : $i, X48 : $i]:
% 0.34/0.61         ((r2_hidden @ (k4_tarski @ X44 @ X46) @ 
% 0.34/0.61           (k2_zfmisc_1 @ X45 @ (k1_tarski @ X48)))
% 0.34/0.61          | ((X46) != (X48))
% 0.34/0.61          | ~ (r2_hidden @ X44 @ X45))),
% 0.34/0.61      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 0.34/0.61  thf('29', plain,
% 0.34/0.61      (![X44 : $i, X45 : $i, X48 : $i]:
% 0.34/0.61         (~ (r2_hidden @ X44 @ X45)
% 0.34/0.61          | (r2_hidden @ (k4_tarski @ X44 @ X48) @ 
% 0.34/0.61             (k2_zfmisc_1 @ X45 @ (k1_tarski @ X48))))),
% 0.34/0.61      inference('simplify', [status(thm)], ['28'])).
% 0.34/0.61  thf('30', plain,
% 0.34/0.61      (![X0 : $i, X1 : $i]:
% 0.34/0.61         (((X0) = (k1_xboole_0))
% 0.34/0.61          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ X1) @ 
% 0.34/0.61             (k2_zfmisc_1 @ X0 @ (k1_tarski @ X1))))),
% 0.34/0.61      inference('sup-', [status(thm)], ['27', '29'])).
% 0.34/0.61  thf('31', plain,
% 0.34/0.61      (((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ sk_B_1) @ k1_xboole_0)
% 0.34/0.61        | ((sk_A) = (k1_xboole_0)))),
% 0.34/0.61      inference('sup+', [status(thm)], ['26', '30'])).
% 0.34/0.61  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 0.34/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.61  thf('33', plain,
% 0.34/0.61      ((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ sk_B_1) @ k1_xboole_0)),
% 0.34/0.61      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.34/0.61  thf('34', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.34/0.61      inference('condensation', [status(thm)], ['21'])).
% 0.34/0.61  thf('35', plain, ($false), inference('sup-', [status(thm)], ['33', '34'])).
% 0.34/0.61  
% 0.34/0.61  % SZS output end Refutation
% 0.34/0.61  
% 0.34/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
