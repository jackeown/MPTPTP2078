%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cwwp64jl6B

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 262 expanded)
%              Number of leaves         :    7 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  291 (2298 expanded)
%              Number of equality atoms :   44 ( 382 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t39_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
      <=> ( ( A = k1_xboole_0 )
          | ( A
            = ( k1_tarski @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_zfmisc_1])).

thf('0',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
      & ( sk_A
        = ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7
        = ( k1_tarski @ X6 ) )
      | ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('9',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('11',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ ( k1_tarski @ X8 ) )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('13',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X8 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('16',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_B ) )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['11','17'])).

thf('19',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['10','18'])).

thf('20',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','19'])).

thf('21',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('22',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['6','23'])).

thf('25',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('26',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( sk_A
    = ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['11','25','6','23','26'])).

thf('28',plain,(
    ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['4','24','27'])).

thf('29',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( sk_A
    = ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['11','25','6','23','26'])).

thf('31',plain,
    ( sk_A
    = ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ ( k1_tarski @ X8 ) )
      | ( X7
       != ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('33',plain,(
    ! [X8: $i] :
      ( r1_tarski @ ( k1_tarski @ X8 ) @ ( k1_tarski @ X8 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['31','33'])).

thf('35',plain,
    ( sk_A
    = ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['29','30'])).

thf('36',plain,(
    r1_tarski @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['28','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cwwp64jl6B
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:05:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 48 iterations in 0.019s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(t39_zfmisc_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.47          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t39_zfmisc_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((((sk_A) = (k1_tarski @ sk_B))
% 0.21/0.47        | ((sk_A) = (k1_xboole_0))
% 0.21/0.47        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((((sk_A) = (k1_tarski @ sk_B))) <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      ((((sk_A) != (k1_xboole_0)) | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.47         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      ((~ (r1_tarski @ sk_A @ sk_A))
% 0.21/0.47         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) & 
% 0.21/0.47             (((sk_A) = (k1_tarski @ sk_B))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      ((((sk_A) != (k1_tarski @ sk_B))
% 0.21/0.47        | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | 
% 0.21/0.47       ~ (((sk_A) = (k1_tarski @ sk_B)))),
% 0.21/0.47      inference('split', [status(esa)], ['5'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.47         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf(l3_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i]:
% 0.21/0.47         (((X7) = (k1_tarski @ X6))
% 0.21/0.47          | ((X7) = (k1_xboole_0))
% 0.21/0.47          | ~ (r1_tarski @ X7 @ (k1_tarski @ X6)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ sk_B))))
% 0.21/0.47         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.21/0.47       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         ((r1_tarski @ X7 @ (k1_tarski @ X8)) | ((X7) != (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.47  thf('13', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X8))),
% 0.21/0.47      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.47         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_B)))
% 0.21/0.47         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) & 
% 0.21/0.47             (((sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.47  thf('18', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['11', '17'])).
% 0.21/0.47  thf('19', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['10', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      ((((sk_A) = (k1_tarski @ sk_B)))
% 0.21/0.47         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['9', '19'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['5'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      ((((sk_A) != (sk_A)))
% 0.21/0.47         <= (~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.21/0.47             ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.21/0.47       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.47  thf('24', plain, (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['6', '23'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (~ (((sk_A) = (k1_xboole_0))) | ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.21/0.47       ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | (((sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('27', plain, ((((sk_A) = (k1_tarski @ sk_B)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['11', '25', '6', '23', '26'])).
% 0.21/0.47  thf('28', plain, (~ (r1_tarski @ sk_A @ sk_A)),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['4', '24', '27'])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      ((((sk_A) = (k1_tarski @ sk_B))) <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('30', plain, ((((sk_A) = (k1_tarski @ sk_B)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['11', '25', '6', '23', '26'])).
% 0.21/0.47  thf('31', plain, (((sk_A) = (k1_tarski @ sk_B))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['29', '30'])).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         ((r1_tarski @ X7 @ (k1_tarski @ X8)) | ((X7) != (k1_tarski @ X8)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      (![X8 : $i]: (r1_tarski @ (k1_tarski @ X8) @ (k1_tarski @ X8))),
% 0.21/0.47      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.47  thf('34', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.47      inference('sup+', [status(thm)], ['31', '33'])).
% 0.21/0.47  thf('35', plain, (((sk_A) = (k1_tarski @ sk_B))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['29', '30'])).
% 0.21/0.47  thf('36', plain, ((r1_tarski @ sk_A @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.47  thf('37', plain, ($false), inference('demod', [status(thm)], ['28', '36'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
