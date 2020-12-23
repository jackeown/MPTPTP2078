%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MjueJoUAj9

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  53 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  164 ( 320 expanded)
%              Number of equality atoms :   23 (  45 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X16 ) )
      | ( X15 = X16 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t24_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t24_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11
        = ( k1_tarski @ X10 ) )
      | ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('3',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_tarski @ X14 ) )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('5',plain,(
    ! [X14: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( ( sk_B = sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X14: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('11',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('13',plain,(
    ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_xboole_0 @ X1 @ X3 )
      | ( ( k4_xboole_0 @ X1 @ X3 )
       != X1 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['13','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MjueJoUAj9
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 26 iterations in 0.016s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(t17_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( A ) != ( B ) ) =>
% 0.21/0.49       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X16))
% 0.21/0.49          | ((X15) = (X16)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.21/0.49  thf(t24_zfmisc_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.21/0.49       ( ( A ) = ( B ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.21/0.49          ( ( A ) = ( B ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t24_zfmisc_1])).
% 0.21/0.49  thf('1', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(l3_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         (((X11) = (k1_tarski @ X10))
% 0.21/0.49          | ((X11) = (k1_xboole_0))
% 0.21/0.49          | ~ (r1_tarski @ X11 @ (k1_tarski @ X10)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.49        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf(t16_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.21/0.49          ( ( A ) = ( B ) ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         (~ (r1_xboole_0 @ (k1_tarski @ X13) @ (k1_tarski @ X14))
% 0.21/0.49          | ((X13) != (X14)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X14 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X14))),
% 0.21/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      ((~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.21/0.49        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.49  thf('7', plain, ((((sk_B) = (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '6'])).
% 0.21/0.49  thf('8', plain, (((sk_A) != (sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('9', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X14 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X14))),
% 0.21/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.49  thf('11', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('13', plain, (~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf(t3_boole, axiom,
% 0.21/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.49  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.49  thf(t83_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X1 : $i, X3 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ X1 @ X3) | ((k4_xboole_0 @ X1 @ X3) != (X1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('17', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.21/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.49  thf('18', plain, ($false), inference('demod', [status(thm)], ['13', '17'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
