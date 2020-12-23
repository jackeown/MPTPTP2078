%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XAKX1dveX1

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:12 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   37 (  63 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  276 ( 547 expanded)
%              Number of equality atoms :   43 (  91 expanded)
%              Maximal formula depth    :    8 (   5 average)

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
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ ( k1_tarski @ X5 ) )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('3',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X5 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X3 ) )
      | ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ ( k1_tarski @ X3 ) ) ) ),
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

thf('20',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
      & ( sk_A
        = ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','24'])).

thf('26',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('27',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','8','10','19','25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XAKX1dveX1
% 0.13/0.37  % Computer   : n016.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 17:51:34 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 33 iterations in 0.016s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.50  thf(t39_zfmisc_1, conjecture,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.24/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.24/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.50    (~( ![A:$i,B:$i]:
% 0.24/0.50        ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.24/0.50          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ) )),
% 0.24/0.50    inference('cnf.neg', [status(esa)], [t39_zfmisc_1])).
% 0.24/0.50  thf('0', plain,
% 0.24/0.50      ((((sk_A) != (k1_xboole_0)) | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('1', plain,
% 0.24/0.50      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.24/0.50       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.24/0.50      inference('split', [status(esa)], ['0'])).
% 0.24/0.50  thf(l3_zfmisc_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.24/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.24/0.50  thf('2', plain,
% 0.24/0.50      (![X4 : $i, X5 : $i]:
% 0.24/0.50         ((r1_tarski @ X4 @ (k1_tarski @ X5)) | ((X4) != (k1_xboole_0)))),
% 0.24/0.50      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.24/0.50  thf('3', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X5))),
% 0.24/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.24/0.50  thf('4', plain,
% 0.24/0.50      ((((sk_A) = (k1_tarski @ sk_B))
% 0.24/0.50        | ((sk_A) = (k1_xboole_0))
% 0.24/0.50        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('5', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.24/0.50      inference('split', [status(esa)], ['4'])).
% 0.24/0.50  thf('6', plain,
% 0.24/0.50      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.24/0.50         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.50      inference('split', [status(esa)], ['0'])).
% 0.24/0.50  thf('7', plain,
% 0.24/0.50      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_B)))
% 0.24/0.50         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) & 
% 0.24/0.50             (((sk_A) = (k1_xboole_0))))),
% 0.24/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.24/0.50  thf('8', plain,
% 0.24/0.50      (~ (((sk_A) = (k1_xboole_0))) | ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['3', '7'])).
% 0.24/0.50  thf('9', plain,
% 0.24/0.50      ((((sk_A) != (k1_tarski @ sk_B))
% 0.24/0.50        | ~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('10', plain,
% 0.24/0.50      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.24/0.50       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.24/0.50      inference('split', [status(esa)], ['9'])).
% 0.24/0.50  thf('11', plain,
% 0.24/0.50      (((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.24/0.50         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.50      inference('split', [status(esa)], ['4'])).
% 0.24/0.50  thf('12', plain,
% 0.24/0.50      (![X3 : $i, X4 : $i]:
% 0.24/0.50         (((X4) = (k1_tarski @ X3))
% 0.24/0.50          | ((X4) = (k1_xboole_0))
% 0.24/0.50          | ~ (r1_tarski @ X4 @ (k1_tarski @ X3)))),
% 0.24/0.50      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.24/0.50  thf('13', plain,
% 0.24/0.50      (((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ sk_B))))
% 0.24/0.50         <= (((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.50  thf('14', plain,
% 0.24/0.50      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 0.24/0.50      inference('split', [status(esa)], ['9'])).
% 0.24/0.50  thf('15', plain,
% 0.24/0.50      (((((sk_A) != (sk_A)) | ((sk_A) = (k1_xboole_0))))
% 0.24/0.50         <= (~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.24/0.50             ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.24/0.50  thf('16', plain,
% 0.24/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.24/0.50         <= (~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.24/0.50             ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.24/0.50  thf('17', plain,
% 0.24/0.50      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.24/0.50      inference('split', [status(esa)], ['0'])).
% 0.24/0.50  thf('18', plain,
% 0.24/0.50      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.24/0.50         <= (~ (((sk_A) = (k1_xboole_0))) & 
% 0.24/0.50             ~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.24/0.50             ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.50  thf('19', plain,
% 0.24/0.50      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.24/0.50       ~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | (((sk_A) = (k1_xboole_0)))),
% 0.24/0.50      inference('simplify', [status(thm)], ['18'])).
% 0.24/0.50  thf('20', plain,
% 0.24/0.50      ((((sk_A) = (k1_tarski @ sk_B))) <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.24/0.50      inference('split', [status(esa)], ['4'])).
% 0.24/0.50  thf('21', plain,
% 0.24/0.50      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))
% 0.24/0.50         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))))),
% 0.24/0.50      inference('split', [status(esa)], ['0'])).
% 0.24/0.50  thf('22', plain,
% 0.24/0.50      ((~ (r1_tarski @ sk_A @ sk_A))
% 0.24/0.50         <= (~ ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) & 
% 0.24/0.50             (((sk_A) = (k1_tarski @ sk_B))))),
% 0.24/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.50  thf(d10_xboole_0, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.50  thf('23', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.24/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.50  thf('24', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.24/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.24/0.50  thf('25', plain,
% 0.24/0.50      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.24/0.50       ((r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.24/0.50      inference('demod', [status(thm)], ['22', '24'])).
% 0.24/0.50  thf('26', plain,
% 0.24/0.50      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.24/0.50       ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))) | (((sk_A) = (k1_xboole_0)))),
% 0.24/0.50      inference('split', [status(esa)], ['4'])).
% 0.24/0.50  thf('27', plain, ($false),
% 0.24/0.50      inference('sat_resolution*', [status(thm)],
% 0.24/0.50                ['1', '8', '10', '19', '25', '26'])).
% 0.24/0.50  
% 0.24/0.50  % SZS output end Refutation
% 0.24/0.50  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
