%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.W1jHN3hPNK

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 112 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :  258 ( 854 expanded)
%              Number of equality atoms :   41 ( 143 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
     != ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
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
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('6',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('8',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('11',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_B ) )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['6','12'])).

thf('14',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['5','13'])).

thf('15',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','14'])).

thf('16',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['3','17','20'])).

thf('22',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','23'])).

thf('25',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','14'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6
        = ( k1_tarski @ X5 ) )
      | ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('27',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['5','13'])).

thf('30',plain,
    ( sk_A
    = ( k1_tarski @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['24','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.W1jHN3hPNK
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:44:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 29 iterations in 0.013s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(t39_zfmisc_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.48          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t39_zfmisc_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((((sk_A) != (k1_tarski @ sk_B))
% 0.21/0.48        | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((((sk_A) != (k1_xboole_0)) | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['2'])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ sk_B))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0))
% 0.21/0.48        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['2'])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.21/0.48       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['2'])).
% 0.21/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.48  thf('7', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ sk_B))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0))
% 0.21/0.48        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('9', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['2'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_B)))
% 0.21/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) & 
% 0.21/0.48             (((sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '11'])).
% 0.21/0.48  thf('13', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['6', '12'])).
% 0.21/0.48  thf('14', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['5', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ sk_B)) | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['4', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['2'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ sk_B)))
% 0.21/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf(t1_boole, axiom,
% 0.21/0.48    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.48  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.48  thf(t7_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.48  thf('20', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.48      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain, (((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['3', '17', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.21/0.48       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('23', plain, (~ (((sk_A) = (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['1', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ sk_B)) | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['4', '14'])).
% 0.21/0.48  thf(l3_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]:
% 0.21/0.48         (((X6) = (k1_tarski @ X5))
% 0.21/0.48          | ((X6) = (k1_xboole_0))
% 0.21/0.48          | ~ (r1_tarski @ X6 @ (k1_tarski @ X5)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ sk_B))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.48  thf('29', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['5', '13'])).
% 0.21/0.48  thf('30', plain, (((sk_A) = (k1_tarski @ sk_B))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.21/0.48  thf('31', plain, (((sk_A) != (sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['24', '30'])).
% 0.21/0.48  thf('32', plain, ($false), inference('simplify', [status(thm)], ['31'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
