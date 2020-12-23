%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NoNYT7Lfr9

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 262 expanded)
%              Number of leaves         :    7 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  291 (2298 expanded)
%              Number of equality atoms :   44 ( 382 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X3: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X3 ) )
      | ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ ( k1_tarski @ X3 ) ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ ( k1_tarski @ X5 ) )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('13',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X5 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ ( k1_tarski @ X5 ) )
      | ( X4
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('33',plain,(
    ! [X5: $i] :
      ( r1_tarski @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X5 ) ) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NoNYT7Lfr9
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 58 iterations in 0.023s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(t39_zfmisc_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.48          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t39_zfmisc_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((((sk_A) = (k1_tarski @ sk_B))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0))
% 0.20/0.48        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((((sk_A) = (k1_tarski @ sk_B))) <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((((sk_A) != (k1_xboole_0)) | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      ((~ (r1_tarski @ sk_A @ sk_A))
% 0.20/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) & 
% 0.20/0.48             (((sk_A) = (k1_tarski @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      ((((sk_A) != (k1_tarski @ sk_B))
% 0.20/0.48        | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | 
% 0.20/0.48       ~ (((sk_A) = (k1_tarski @ sk_B)))),
% 0.20/0.48      inference('split', [status(esa)], ['5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.48         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf(l3_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (((X4) = (k1_tarski @ X3))
% 0.20/0.48          | ((X4) = (k1_xboole_0))
% 0.20/0.48          | ~ (r1_tarski @ X4 @ (k1_tarski @ X3)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ sk_B))))
% 0.20/0.48         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.20/0.48       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         ((r1_tarski @ X4 @ (k1_tarski @ X5)) | ((X4) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.48  thf('13', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X5))),
% 0.20/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_B)))
% 0.20/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) & 
% 0.20/0.48             (((sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '16'])).
% 0.20/0.48  thf('18', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['11', '17'])).
% 0.20/0.48  thf('19', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['10', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      ((((sk_A) = (k1_tarski @ sk_B)))
% 0.20/0.48         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['9', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 0.20/0.48      inference('split', [status(esa)], ['5'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      ((((sk_A) != (sk_A)))
% 0.20/0.48         <= (~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.20/0.48             ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.20/0.48       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.48  thf('24', plain, (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['6', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (~ (((sk_A) = (k1_xboole_0))) | ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '16'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.20/0.48       ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | (((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('27', plain, ((((sk_A) = (k1_tarski @ sk_B)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['11', '25', '6', '23', '26'])).
% 0.20/0.48  thf('28', plain, (~ (r1_tarski @ sk_A @ sk_A)),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['4', '24', '27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      ((((sk_A) = (k1_tarski @ sk_B))) <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('30', plain, ((((sk_A) = (k1_tarski @ sk_B)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['11', '25', '6', '23', '26'])).
% 0.20/0.48  thf('31', plain, (((sk_A) = (k1_tarski @ sk_B))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         ((r1_tarski @ X4 @ (k1_tarski @ X5)) | ((X4) != (k1_tarski @ X5)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X5 : $i]: (r1_tarski @ (k1_tarski @ X5) @ (k1_tarski @ X5))),
% 0.20/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.48  thf('34', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.48      inference('sup+', [status(thm)], ['31', '33'])).
% 0.20/0.48  thf('35', plain, (((sk_A) = (k1_tarski @ sk_B))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('36', plain, ((r1_tarski @ sk_A @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('37', plain, ($false), inference('demod', [status(thm)], ['28', '36'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
