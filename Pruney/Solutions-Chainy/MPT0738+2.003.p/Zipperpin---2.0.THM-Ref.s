%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P9Uhoph3Bp

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:48 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   44 (  61 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :  210 ( 380 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ~ ( v3_ordinal1 @ X8 )
      | ( r1_ordinal1 @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t26_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r1_ordinal1 @ A @ B )
              | ( r2_hidden @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_ordinal1])).

thf('5',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_ordinal1 @ X9 )
      | ( r2_hidden @ X10 @ X9 )
      | ( X10 = X9 )
      | ( r2_hidden @ X9 @ X10 )
      | ~ ( v3_ordinal1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('7',plain,(
    ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v3_ordinal1 @ sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r1_tarski @ X4 @ X5 )
      | ~ ( v1_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('13',plain,
    ( ( sk_B_1 = sk_A )
    | ~ ( v1_ordinal1 @ sk_B_1 )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( ( v1_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('16',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B_1 = sk_A )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ~ ( v3_ordinal1 @ X8 )
      | ( r1_ordinal1 @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('19',plain,
    ( ( sk_B_1 = sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_B_1 = sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_B_1 = sk_A ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['5','24'])).

thf('26',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','25'])).

thf('27',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P9Uhoph3Bp
% 0.15/0.36  % Computer   : n010.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 11:15:59 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 29 iterations in 0.016s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.23/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.49  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.23/0.49  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.23/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.49  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.23/0.49  thf(d10_xboole_0, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.49  thf('0', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.23/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.49  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.23/0.49      inference('simplify', [status(thm)], ['0'])).
% 0.23/0.49  thf(redefinition_r1_ordinal1, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.23/0.49       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.23/0.49  thf('2', plain,
% 0.23/0.49      (![X7 : $i, X8 : $i]:
% 0.23/0.49         (~ (v3_ordinal1 @ X7)
% 0.23/0.49          | ~ (v3_ordinal1 @ X8)
% 0.23/0.49          | (r1_ordinal1 @ X7 @ X8)
% 0.23/0.49          | ~ (r1_tarski @ X7 @ X8))),
% 0.23/0.49      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.23/0.49  thf('3', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.23/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.49  thf('4', plain,
% 0.23/0.49      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0))),
% 0.23/0.49      inference('simplify', [status(thm)], ['3'])).
% 0.23/0.49  thf(t26_ordinal1, conjecture,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( v3_ordinal1 @ A ) =>
% 0.23/0.49       ( ![B:$i]:
% 0.23/0.49         ( ( v3_ordinal1 @ B ) =>
% 0.23/0.49           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i]:
% 0.23/0.49        ( ( v3_ordinal1 @ A ) =>
% 0.23/0.49          ( ![B:$i]:
% 0.23/0.49            ( ( v3_ordinal1 @ B ) =>
% 0.23/0.49              ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t26_ordinal1])).
% 0.23/0.49  thf('5', plain, (~ (r1_ordinal1 @ sk_A @ sk_B_1)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(t24_ordinal1, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( v3_ordinal1 @ A ) =>
% 0.23/0.49       ( ![B:$i]:
% 0.23/0.49         ( ( v3_ordinal1 @ B ) =>
% 0.23/0.49           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.23/0.49                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.23/0.49  thf('6', plain,
% 0.23/0.49      (![X9 : $i, X10 : $i]:
% 0.23/0.49         (~ (v3_ordinal1 @ X9)
% 0.23/0.49          | (r2_hidden @ X10 @ X9)
% 0.23/0.49          | ((X10) = (X9))
% 0.23/0.49          | (r2_hidden @ X9 @ X10)
% 0.23/0.49          | ~ (v3_ordinal1 @ X10))),
% 0.23/0.49      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.23/0.49  thf('7', plain, (~ (r2_hidden @ sk_B_1 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('8', plain,
% 0.23/0.49      ((~ (v3_ordinal1 @ sk_B_1)
% 0.23/0.49        | (r2_hidden @ sk_A @ sk_B_1)
% 0.23/0.49        | ((sk_B_1) = (sk_A))
% 0.23/0.49        | ~ (v3_ordinal1 @ sk_A))),
% 0.23/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.49  thf('9', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('10', plain, ((v3_ordinal1 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('11', plain, (((r2_hidden @ sk_A @ sk_B_1) | ((sk_B_1) = (sk_A)))),
% 0.23/0.49      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.23/0.49  thf(d2_ordinal1, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( v1_ordinal1 @ A ) <=>
% 0.23/0.49       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.23/0.49  thf('12', plain,
% 0.23/0.49      (![X4 : $i, X5 : $i]:
% 0.23/0.49         (~ (r2_hidden @ X4 @ X5)
% 0.23/0.49          | (r1_tarski @ X4 @ X5)
% 0.23/0.49          | ~ (v1_ordinal1 @ X5))),
% 0.23/0.49      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.23/0.49  thf('13', plain,
% 0.23/0.49      ((((sk_B_1) = (sk_A))
% 0.23/0.49        | ~ (v1_ordinal1 @ sk_B_1)
% 0.23/0.49        | (r1_tarski @ sk_A @ sk_B_1))),
% 0.23/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.49  thf('14', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(cc1_ordinal1, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.23/0.49  thf('15', plain, (![X3 : $i]: ((v1_ordinal1 @ X3) | ~ (v3_ordinal1 @ X3))),
% 0.23/0.49      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.23/0.49  thf('16', plain, ((v1_ordinal1 @ sk_B_1)),
% 0.23/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.49  thf('17', plain, ((((sk_B_1) = (sk_A)) | (r1_tarski @ sk_A @ sk_B_1))),
% 0.23/0.49      inference('demod', [status(thm)], ['13', '16'])).
% 0.23/0.49  thf('18', plain,
% 0.23/0.49      (![X7 : $i, X8 : $i]:
% 0.23/0.49         (~ (v3_ordinal1 @ X7)
% 0.23/0.49          | ~ (v3_ordinal1 @ X8)
% 0.23/0.49          | (r1_ordinal1 @ X7 @ X8)
% 0.23/0.49          | ~ (r1_tarski @ X7 @ X8))),
% 0.23/0.49      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.23/0.49  thf('19', plain,
% 0.23/0.49      ((((sk_B_1) = (sk_A))
% 0.23/0.49        | (r1_ordinal1 @ sk_A @ sk_B_1)
% 0.23/0.49        | ~ (v3_ordinal1 @ sk_B_1)
% 0.23/0.49        | ~ (v3_ordinal1 @ sk_A))),
% 0.23/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.23/0.49  thf('20', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('21', plain, ((v3_ordinal1 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('22', plain, ((((sk_B_1) = (sk_A)) | (r1_ordinal1 @ sk_A @ sk_B_1))),
% 0.23/0.49      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.23/0.49  thf('23', plain, (~ (r1_ordinal1 @ sk_A @ sk_B_1)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('24', plain, (((sk_B_1) = (sk_A))),
% 0.23/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.23/0.49  thf('25', plain, (~ (r1_ordinal1 @ sk_A @ sk_A)),
% 0.23/0.49      inference('demod', [status(thm)], ['5', '24'])).
% 0.23/0.49  thf('26', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.23/0.49      inference('sup-', [status(thm)], ['4', '25'])).
% 0.23/0.49  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('28', plain, ($false), inference('demod', [status(thm)], ['26', '27'])).
% 0.23/0.49  
% 0.23/0.49  % SZS output end Refutation
% 0.23/0.49  
% 0.23/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
