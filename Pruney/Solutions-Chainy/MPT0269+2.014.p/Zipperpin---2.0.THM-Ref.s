%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g17Gklupko

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 104 expanded)
%              Number of leaves         :   17 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :  370 ( 803 expanded)
%              Number of equality atoms :   42 ( 109 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ( ( k4_xboole_0 @ X16 @ X17 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('2',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( ( k1_tarski @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','13'])).

thf('15',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X16: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X18 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['23'])).

thf('25',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['16','24'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('26',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ( X28 = X25 )
      | ( X27
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('27',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28 = X25 )
      | ~ ( r2_hidden @ X28 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( sk_B @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('30',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r2_hidden @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X36: $i,X38: $i,X39: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X36 @ X38 ) @ X39 )
      | ~ ( r2_hidden @ X38 @ X39 )
      | ~ ( r2_hidden @ X36 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ ( k2_tarski @ ( sk_B @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','34'])).

thf('36',plain,
    ( ( sk_B @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['25','27'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('37',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['7','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g17Gklupko
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 119 iterations in 0.066s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(t66_zfmisc_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.21/0.53          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i]:
% 0.21/0.53        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.21/0.53             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(l32_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i]:
% 0.21/0.53         ((r1_tarski @ X16 @ X17)
% 0.21/0.53          | ((k4_xboole_0 @ X16 @ X17) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.53        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.53  thf('3', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.21/0.53      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X13 : $i, X15 : $i]:
% 0.21/0.53         (((X13) = (X15))
% 0.21/0.53          | ~ (r1_tarski @ X15 @ X13)
% 0.21/0.53          | ~ (r1_tarski @ X13 @ X15))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      ((~ (r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.21/0.53        | ((k1_tarski @ sk_B_1) = (sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf('6', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('7', plain, (~ (r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf(t7_xboole_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X12 : $i]:
% 0.21/0.53         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X12 : $i]:
% 0.21/0.53         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.53  thf(d5_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.53       ( ![D:$i]:
% 0.21/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.53           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X2 @ X3)
% 0.21/0.53          | (r2_hidden @ X2 @ X4)
% 0.21/0.53          | (r2_hidden @ X2 @ X5)
% 0.21/0.53          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.53         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.21/0.53          | (r2_hidden @ X2 @ X4)
% 0.21/0.53          | ~ (r2_hidden @ X2 @ X3))),
% 0.21/0.53      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((X0) = (k1_xboole_0))
% 0.21/0.53          | (r2_hidden @ (sk_B @ X0) @ X1)
% 0.21/0.53          | (r2_hidden @ (sk_B @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (((r2_hidden @ (sk_B @ sk_A) @ k1_xboole_0)
% 0.21/0.53        | (r2_hidden @ (sk_B @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.21/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['9', '13'])).
% 0.21/0.53  thf('15', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (((r2_hidden @ (sk_B @ sk_A) @ k1_xboole_0)
% 0.21/0.53        | (r2_hidden @ (sk_B @ sk_A) @ (k1_tarski @ sk_B_1)))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]: ((r1_tarski @ X13 @ X14) | ((X13) != (X14)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('18', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.21/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X16 : $i, X18 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ X16 @ X18) = (k1_xboole_0))
% 0.21/0.53          | ~ (r1_tarski @ X16 @ X18))),
% 0.21/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.53  thf('20', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X6 @ X5)
% 0.21/0.53          | ~ (r2_hidden @ X6 @ X4)
% 0.21/0.53          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X6 @ X4)
% 0.21/0.53          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['20', '22'])).
% 0.21/0.53  thf('24', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.53      inference('condensation', [status(thm)], ['23'])).
% 0.21/0.53  thf('25', plain, ((r2_hidden @ (sk_B @ sk_A) @ (k1_tarski @ sk_B_1))),
% 0.21/0.53      inference('clc', [status(thm)], ['16', '24'])).
% 0.21/0.53  thf(d1_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X28 @ X27)
% 0.21/0.53          | ((X28) = (X25))
% 0.21/0.53          | ((X27) != (k1_tarski @ X25)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X25 : $i, X28 : $i]:
% 0.21/0.53         (((X28) = (X25)) | ~ (r2_hidden @ X28 @ (k1_tarski @ X25)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.53  thf('28', plain, (((sk_B @ sk_A) = (sk_B_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['25', '27'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X12 : $i]:
% 0.21/0.53         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.53  thf('30', plain, (((r2_hidden @ sk_B_1 @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['28', '29'])).
% 0.21/0.53  thf('31', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('32', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.21/0.53  thf(t38_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.53       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X36 : $i, X38 : $i, X39 : $i]:
% 0.21/0.53         ((r1_tarski @ (k2_tarski @ X36 @ X38) @ X39)
% 0.21/0.53          | ~ (r2_hidden @ X38 @ X39)
% 0.21/0.53          | ~ (r2_hidden @ X36 @ X39))),
% 0.21/0.53      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.53          | (r1_tarski @ (k2_tarski @ X0 @ sk_B_1) @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      ((((sk_A) = (k1_xboole_0))
% 0.21/0.53        | (r1_tarski @ (k2_tarski @ (sk_B @ sk_A) @ sk_B_1) @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '34'])).
% 0.21/0.53  thf('36', plain, (((sk_B @ sk_A) = (sk_B_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['25', '27'])).
% 0.21/0.53  thf(t69_enumset1, axiom,
% 0.21/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 0.21/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      ((((sk_A) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.21/0.53  thf('39', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('40', plain, ((r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.21/0.53  thf('41', plain, ($false), inference('demod', [status(thm)], ['7', '40'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
