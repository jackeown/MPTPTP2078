%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V8PgIlOFkr

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  55 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  180 ( 343 expanded)
%              Number of equality atoms :   28 (  55 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t24_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t24_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20
        = ( k1_tarski @ X19 ) )
      | ( X20 = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('2',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X5 != X4 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('4',plain,(
    ! [X4: $i] :
      ( r2_hidden @ X4 @ ( k1_tarski @ X4 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( X7 = X4 )
      | ( X6
       != ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X23 ) )
      | ( X22 != X23 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('12',plain,(
    ! [X23: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_tarski @ X23 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_xboole_0 @ X1 @ X3 )
      | ( ( k4_xboole_0 @ X1 @ X3 )
       != X1 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['13','14','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V8PgIlOFkr
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:56:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 50 iterations in 0.022s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(t24_zfmisc_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.21/0.49       ( ( A ) = ( B ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.21/0.49          ( ( A ) = ( B ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t24_zfmisc_1])).
% 0.21/0.49  thf('0', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(l3_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X19 : $i, X20 : $i]:
% 0.21/0.49         (((X20) = (k1_tarski @ X19))
% 0.21/0.49          | ((X20) = (k1_xboole_0))
% 0.21/0.49          | ~ (r1_tarski @ X20 @ (k1_tarski @ X19)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.49        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(d1_tarski, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (((X5) != (X4)) | (r2_hidden @ X5 @ X6) | ((X6) != (k1_tarski @ X4)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.49  thf('4', plain, (![X4 : $i]: (r2_hidden @ X4 @ (k1_tarski @ X4))),
% 0.21/0.49      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 0.21/0.49        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['2', '4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X7 @ X6) | ((X7) = (X4)) | ((X6) != (k1_tarski @ X4)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X4 : $i, X7 : $i]:
% 0.21/0.49         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.49  thf('8', plain, ((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_B) = (sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.49  thf('9', plain, (((sk_A) != (sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('10', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf(t16_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.21/0.49          ( ( A ) = ( B ) ) ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X22 : $i, X23 : $i]:
% 0.21/0.49         (~ (r1_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X23))
% 0.21/0.49          | ((X22) != (X23)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X23 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X23) @ (k1_tarski @ X23))),
% 0.21/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.49  thf('13', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.49  thf('14', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf(t3_boole, axiom,
% 0.21/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.49  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.49  thf(t83_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X1 : $i, X3 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ X1 @ X3) | ((k4_xboole_0 @ X1 @ X3) != (X1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.21/0.49      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.49  thf('19', plain, ($false),
% 0.21/0.49      inference('demod', [status(thm)], ['13', '14', '18'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
