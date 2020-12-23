%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CvNOFjUHPQ

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  50 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  180 ( 367 expanded)
%              Number of equality atoms :   29 (  60 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t66_xboole_1,conjecture,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( ( A != k1_xboole_0 )
            & ( r1_xboole_0 @ A @ A ) )
        & ~ ( ~ ( r1_xboole_0 @ A @ A )
            & ( A = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_xboole_1])).

thf('0',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('5',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('6',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('7',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_A != k1_xboole_0 )
      & ( r1_xboole_0 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('12',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_A )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ k1_xboole_0 )
   <= ( ~ ( r1_xboole_0 @ sk_A @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('20',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( r1_xboole_0 @ sk_A @ sk_A )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','10','11','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CvNOFjUHPQ
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:41:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 19 iterations in 0.010s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.47  thf(t66_xboole_1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.21/0.47       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.21/0.47          ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t66_xboole_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((((sk_A) != (k1_xboole_0)) | ~ (r1_xboole_0 @ sk_A @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (~ (((sk_A) = (k1_xboole_0))) | ~ ((r1_xboole_0 @ sk_A @ sk_A))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('2', plain, (((r1_xboole_0 @ sk_A @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (((r1_xboole_0 @ sk_A @ sk_A)) <= (((r1_xboole_0 @ sk_A @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf(d7_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.21/0.47       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      ((((k3_xboole_0 @ sk_A @ sk_A) = (k1_xboole_0)))
% 0.21/0.47         <= (((r1_xboole_0 @ sk_A @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.47  thf('6', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      ((((sk_A) = (k1_xboole_0))) <= (((r1_xboole_0 @ sk_A @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.47         <= (~ (((sk_A) = (k1_xboole_0))) & ((r1_xboole_0 @ sk_A @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((((sk_A) = (k1_xboole_0))) | ~ ((r1_xboole_0 @ sk_A @ sk_A))),
% 0.21/0.47      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      ((((sk_A) = (k1_xboole_0))) | ((r1_xboole_0 @ sk_A @ sk_A))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('12', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X0 : $i, X2 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      ((~ (r1_xboole_0 @ sk_A @ sk_A)) <= (~ ((r1_xboole_0 @ sk_A @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      ((~ (r1_xboole_0 @ sk_A @ k1_xboole_0))
% 0.21/0.47         <= (~ ((r1_xboole_0 @ sk_A @ sk_A)) & (((sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      ((~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.21/0.47         <= (~ ((r1_xboole_0 @ sk_A @ sk_A)) & (((sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (~ (((sk_A) = (k1_xboole_0))) | ((r1_xboole_0 @ sk_A @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['15', '20'])).
% 0.21/0.47  thf('22', plain, ($false),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['1', '10', '11', '21'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
