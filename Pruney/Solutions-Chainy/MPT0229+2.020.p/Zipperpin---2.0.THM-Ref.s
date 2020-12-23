%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VdZC5Hx8V9

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:09 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   47 (  56 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  250 ( 332 expanded)
%              Number of equality atoms :   27 (  41 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X29
        = ( k1_tarski @ X28 ) )
      | ( X29 = k1_xboole_0 )
      | ~ ( r1_tarski @ X29 @ ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('2',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X14 != X13 )
      | ( r2_hidden @ X14 @ X15 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('4',plain,(
    ! [X13: $i] :
      ( r2_hidden @ X13 @ ( k1_tarski @ X13 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( X16 = X13 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_B_1 = sk_A ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X13: $i] :
      ( r2_hidden @ X13 @ ( k1_tarski @ X13 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ X29 @ ( k1_tarski @ X30 ) )
      | ( X29 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('16',plain,(
    ! [X30: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X30 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k4_xboole_0 @ X10 @ X12 )
       != X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X13: $i] :
      ( r2_hidden @ X13 @ ( k1_tarski @ X13 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('23',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('24',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['14','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VdZC5Hx8V9
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:24:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 121 iterations in 0.051s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(t24_zfmisc_1, conjecture,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.36/0.55       ( ( A ) = ( B ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i,B:$i]:
% 0.36/0.55        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.36/0.55          ( ( A ) = ( B ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t24_zfmisc_1])).
% 0.36/0.55  thf('0', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(l3_zfmisc_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.36/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      (![X28 : $i, X29 : $i]:
% 0.36/0.55         (((X29) = (k1_tarski @ X28))
% 0.36/0.55          | ((X29) = (k1_xboole_0))
% 0.36/0.55          | ~ (r1_tarski @ X29 @ (k1_tarski @ X28)))),
% 0.36/0.55      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.36/0.55        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_B_1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.55  thf(d1_tarski, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.36/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.55         (((X14) != (X13))
% 0.36/0.55          | (r2_hidden @ X14 @ X15)
% 0.36/0.55          | ((X15) != (k1_tarski @ X13)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.36/0.55  thf('4', plain, (![X13 : $i]: (r2_hidden @ X13 @ (k1_tarski @ X13))),
% 0.36/0.55      inference('simplify', [status(thm)], ['3'])).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (((r2_hidden @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.36/0.55        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['2', '4'])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X16 @ X15)
% 0.36/0.55          | ((X16) = (X13))
% 0.36/0.55          | ((X15) != (k1_tarski @ X13)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X13 : $i, X16 : $i]:
% 0.36/0.55         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['6'])).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      ((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_B_1) = (sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['5', '7'])).
% 0.36/0.55  thf('9', plain, (((sk_A) != (sk_B_1))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('10', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.36/0.55      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.36/0.55  thf('11', plain, (![X13 : $i]: (r2_hidden @ X13 @ (k1_tarski @ X13))),
% 0.36/0.55      inference('simplify', [status(thm)], ['3'])).
% 0.36/0.55  thf(d1_xboole_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.55  thf('13', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.55  thf('14', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.55      inference('sup-', [status(thm)], ['10', '13'])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (![X29 : $i, X30 : $i]:
% 0.36/0.55         ((r1_tarski @ X29 @ (k1_tarski @ X30)) | ((X29) != (k1_xboole_0)))),
% 0.36/0.55      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      (![X30 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X30))),
% 0.36/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.36/0.55  thf(l32_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      (![X7 : $i, X9 : $i]:
% 0.36/0.55         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.36/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.55  thf(t83_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      (![X10 : $i, X12 : $i]:
% 0.36/0.55         ((r1_xboole_0 @ X10 @ X12) | ((k4_xboole_0 @ X10 @ X12) != (X10)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.55          | (r1_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.36/0.55  thf('22', plain, (![X13 : $i]: (r2_hidden @ X13 @ (k1_tarski @ X13))),
% 0.36/0.55      inference('simplify', [status(thm)], ['3'])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.36/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.55  thf(t3_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.36/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.36/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.36/0.55            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X5 @ X3)
% 0.36/0.55          | ~ (r2_hidden @ X5 @ X6)
% 0.36/0.55          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.36/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((v1_xboole_0 @ X0)
% 0.36/0.55          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.36/0.55          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (r1_xboole_0 @ X0 @ (k1_tarski @ (sk_B @ X0))) | (v1_xboole_0 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['22', '25'])).
% 0.36/0.55  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.55      inference('sup-', [status(thm)], ['21', '26'])).
% 0.36/0.55  thf('28', plain, ($false), inference('demod', [status(thm)], ['14', '27'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
