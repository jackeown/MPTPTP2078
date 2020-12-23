%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0uF4rdPwhf

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  66 expanded)
%              Number of leaves         :   10 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  281 ( 552 expanded)
%              Number of equality atoms :   43 (  91 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ ( k1_tarski @ X8 ) )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('3',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X8 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_B ) )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7
        = ( k1_tarski @ X6 ) )
      | ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('13',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['9'])).

thf('15',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_A != k1_xboole_0 )
      & ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('24',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
      & ( sk_A
        = ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('28',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','8','10','19','26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0uF4rdPwhf
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:35:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 39 iterations in 0.018s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
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
% 0.21/0.47      ((((sk_A) != (k1_xboole_0)) | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.21/0.47       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf(l3_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         ((r1_tarski @ X7 @ (k1_tarski @ X8)) | ((X7) != (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.47  thf('3', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X8))),
% 0.21/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      ((((sk_A) = (k1_tarski @ sk_B))
% 0.21/0.47        | ((sk_A) = (k1_xboole_0))
% 0.21/0.47        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('5', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['4'])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.47         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_B)))
% 0.21/0.47         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) & 
% 0.21/0.47             (((sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (~ (((sk_A) = (k1_xboole_0))) | ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      ((((sk_A) != (k1_tarski @ sk_B))
% 0.21/0.47        | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.21/0.47       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.47      inference('split', [status(esa)], ['9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.47         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['4'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i]:
% 0.21/0.47         (((X7) = (k1_tarski @ X6))
% 0.21/0.47          | ((X7) = (k1_xboole_0))
% 0.21/0.47          | ~ (r1_tarski @ X7 @ (k1_tarski @ X6)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ sk_B))))
% 0.21/0.47         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['9'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (((((sk_A) != (sk_A)) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.47         <= (~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.21/0.47             ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.47         <= (~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.21/0.47             ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((sk_A) = (k1_xboole_0))) & 
% 0.21/0.48             ~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.21/0.48             ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.21/0.48       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | (((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.48  thf(t1_boole, axiom,
% 0.21/0.48    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.48  thf('20', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.48  thf(t7_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.48  thf('22', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.48      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ sk_B))) <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['4'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.21/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      ((~ (r1_tarski @ sk_A @ sk_A))
% 0.21/0.48         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) & 
% 0.21/0.48             (((sk_A) = (k1_tarski @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.21/0.48       ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['22', '25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.21/0.48       ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | (((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('split', [status(esa)], ['4'])).
% 0.21/0.48  thf('28', plain, ($false),
% 0.21/0.48      inference('sat_resolution*', [status(thm)],
% 0.21/0.48                ['1', '8', '10', '19', '26', '27'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
