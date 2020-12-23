%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w7C2Zy8ycI

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:52 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   46 (  65 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  253 ( 389 expanded)
%              Number of equality atoms :   34 (  52 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X14 != X13 )
      | ( r2_hidden @ X14 @ X15 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X13: $i] :
      ( r2_hidden @ X13 @ ( k1_tarski @ X13 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t6_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t6_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X29
        = ( k1_tarski @ X28 ) )
      | ( X29 = k1_xboole_0 )
      | ~ ( r1_tarski @ X29 @ ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('4',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( X16 = X13 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( X0 = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( sk_A = sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','7'])).

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
    inference(simplify,[status(thm)],['0'])).

thf('12',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    $false ),
    inference('sup-',[status(thm)],['12','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w7C2Zy8ycI
% 0.15/0.38  % Computer   : n004.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 19:17:09 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.53  % Solved by: fo/fo7.sh
% 0.24/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.53  % done 79 iterations in 0.040s
% 0.24/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.53  % SZS output start Refutation
% 0.24/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.24/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.24/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.53  thf(d1_tarski, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.24/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.24/0.53  thf('0', plain,
% 0.24/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.24/0.53         (((X14) != (X13))
% 0.24/0.53          | (r2_hidden @ X14 @ X15)
% 0.24/0.53          | ((X15) != (k1_tarski @ X13)))),
% 0.24/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.24/0.53  thf('1', plain, (![X13 : $i]: (r2_hidden @ X13 @ (k1_tarski @ X13))),
% 0.24/0.53      inference('simplify', [status(thm)], ['0'])).
% 0.24/0.53  thf(t6_zfmisc_1, conjecture,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.24/0.53       ( ( A ) = ( B ) ) ))).
% 0.24/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.53    (~( ![A:$i,B:$i]:
% 0.24/0.53        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.24/0.53          ( ( A ) = ( B ) ) ) )),
% 0.24/0.53    inference('cnf.neg', [status(esa)], [t6_zfmisc_1])).
% 0.24/0.53  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(l3_zfmisc_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.24/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.24/0.53  thf('3', plain,
% 0.24/0.53      (![X28 : $i, X29 : $i]:
% 0.24/0.53         (((X29) = (k1_tarski @ X28))
% 0.24/0.53          | ((X29) = (k1_xboole_0))
% 0.24/0.53          | ~ (r1_tarski @ X29 @ (k1_tarski @ X28)))),
% 0.24/0.53      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.24/0.53  thf('4', plain,
% 0.24/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.24/0.53        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_B_1)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.53  thf('5', plain,
% 0.24/0.53      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X16 @ X15)
% 0.24/0.53          | ((X16) = (X13))
% 0.24/0.53          | ((X15) != (k1_tarski @ X13)))),
% 0.24/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.24/0.53  thf('6', plain,
% 0.24/0.53      (![X13 : $i, X16 : $i]:
% 0.24/0.53         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 0.24/0.53      inference('simplify', [status(thm)], ['5'])).
% 0.24/0.53  thf('7', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.24/0.53          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.24/0.53          | ((X0) = (sk_B_1)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['4', '6'])).
% 0.24/0.53  thf('8', plain,
% 0.24/0.53      ((((sk_A) = (sk_B_1)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['1', '7'])).
% 0.24/0.53  thf('9', plain, (((sk_A) != (sk_B_1))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('10', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.24/0.53      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.24/0.53  thf('11', plain, (![X13 : $i]: (r2_hidden @ X13 @ (k1_tarski @ X13))),
% 0.24/0.53      inference('simplify', [status(thm)], ['0'])).
% 0.24/0.53  thf('12', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.24/0.53      inference('sup+', [status(thm)], ['10', '11'])).
% 0.24/0.53  thf(t17_xboole_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.24/0.53  thf('13', plain,
% 0.24/0.53      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.24/0.53      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.24/0.53  thf(t3_xboole_1, axiom,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.53  thf('14', plain,
% 0.24/0.53      (![X12 : $i]:
% 0.24/0.53         (((X12) = (k1_xboole_0)) | ~ (r1_tarski @ X12 @ k1_xboole_0))),
% 0.24/0.53      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.24/0.53  thf('15', plain,
% 0.24/0.53      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.24/0.53  thf(t100_xboole_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.24/0.53  thf('16', plain,
% 0.24/0.53      (![X7 : $i, X8 : $i]:
% 0.24/0.53         ((k4_xboole_0 @ X7 @ X8)
% 0.24/0.53           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.24/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.24/0.53  thf('17', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.24/0.53           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.24/0.53      inference('sup+', [status(thm)], ['15', '16'])).
% 0.24/0.53  thf('18', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.24/0.53           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.24/0.53      inference('sup+', [status(thm)], ['15', '16'])).
% 0.24/0.53  thf('19', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.24/0.53           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.24/0.53      inference('sup+', [status(thm)], ['15', '16'])).
% 0.24/0.53  thf('20', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]:
% 0.24/0.53         ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.24/0.53      inference('sup+', [status(thm)], ['18', '19'])).
% 0.24/0.53  thf(t3_boole, axiom,
% 0.24/0.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.24/0.53  thf('21', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.24/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.24/0.53  thf('22', plain,
% 0.24/0.53      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.24/0.53      inference('sup+', [status(thm)], ['20', '21'])).
% 0.24/0.53  thf('23', plain,
% 0.24/0.53      (((k1_xboole_0) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.24/0.53      inference('demod', [status(thm)], ['17', '22'])).
% 0.24/0.53  thf(t1_xboole_0, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.24/0.53       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.24/0.53  thf('24', plain,
% 0.24/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X3 @ X4)
% 0.24/0.53          | ~ (r2_hidden @ X3 @ X5)
% 0.24/0.53          | ~ (r2_hidden @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 0.24/0.53      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.24/0.53  thf('25', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.24/0.53          | ~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.24/0.53          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.24/0.53  thf('26', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.24/0.53      inference('simplify', [status(thm)], ['25'])).
% 0.24/0.53  thf('27', plain, ($false), inference('sup-', [status(thm)], ['12', '26'])).
% 0.24/0.53  
% 0.24/0.53  % SZS output end Refutation
% 0.24/0.53  
% 0.24/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
