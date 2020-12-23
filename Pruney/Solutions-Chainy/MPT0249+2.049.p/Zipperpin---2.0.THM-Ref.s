%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.48lyBscX7F

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 160 expanded)
%              Number of leaves         :   19 (  53 expanded)
%              Depth                    :   16
%              Number of atoms          :  348 (1312 expanded)
%              Number of equality atoms :   52 ( 262 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('4',plain,(
    ! [X44: $i,X45: $i] :
      ( ( X45
        = ( k1_tarski @ X44 ) )
      | ( X45 = k1_xboole_0 )
      | ~ ( r1_tarski @ X45 @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('5',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('8',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','7'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','14'])).

thf('16',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('19',plain,(
    r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( X14 = X11 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( sk_B @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('26',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X49: $i,X51: $i,X52: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X49 @ X51 ) @ X52 )
      | ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( r2_hidden @ X49 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k2_tarski @ ( sk_B @ sk_C_1 ) @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','30'])).

thf('32',plain,
    ( ( sk_B @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','23'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('33',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('35',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('39',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    sk_B_1 = sk_C_1 ),
    inference('sup+',[status(thm)],['8','39'])).

thf('41',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.48lyBscX7F
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.60  % Solved by: fo/fo7.sh
% 0.21/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.60  % done 515 iterations in 0.151s
% 0.21/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.60  % SZS output start Refutation
% 0.21/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.60  thf(t44_zfmisc_1, conjecture,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.60          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.60          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.60        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.60             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.60             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.60    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.21/0.60  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(t7_xboole_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.60  thf('2', plain,
% 0.21/0.60      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.21/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.60  thf('3', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.21/0.60      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.60  thf(l3_zfmisc_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.60  thf('4', plain,
% 0.21/0.60      (![X44 : $i, X45 : $i]:
% 0.21/0.60         (((X45) = (k1_tarski @ X44))
% 0.21/0.60          | ((X45) = (k1_xboole_0))
% 0.21/0.60          | ~ (r1_tarski @ X45 @ (k1_tarski @ X44)))),
% 0.21/0.60      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.60  thf('5', plain,
% 0.21/0.60      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.60  thf('6', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('7', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.21/0.60      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.21/0.60  thf('8', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.21/0.60      inference('demod', [status(thm)], ['0', '7'])).
% 0.21/0.60  thf(t7_xboole_0, axiom,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.60          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.60  thf('9', plain,
% 0.21/0.60      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.21/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.60  thf('10', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('11', plain,
% 0.21/0.60      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.21/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.60  thf(d3_xboole_0, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.21/0.60       ( ![D:$i]:
% 0.21/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.60           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.60  thf('12', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.60          | (r2_hidden @ X0 @ X2)
% 0.21/0.60          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.21/0.60      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.21/0.60  thf('13', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.21/0.60         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.60  thf('14', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         (((X0) = (k1_xboole_0))
% 0.21/0.60          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['11', '13'])).
% 0.21/0.60  thf('15', plain,
% 0.21/0.60      (((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))
% 0.21/0.60        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.60      inference('sup+', [status(thm)], ['10', '14'])).
% 0.21/0.60  thf('16', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('17', plain, ((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))),
% 0.21/0.60      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.21/0.60  thf('18', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.21/0.60      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.21/0.60  thf('19', plain, ((r2_hidden @ (sk_B @ sk_C_1) @ sk_B_1)),
% 0.21/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.60  thf('20', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.21/0.60      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.21/0.60  thf(d1_tarski, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.60  thf('21', plain,
% 0.21/0.60      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X14 @ X13)
% 0.21/0.60          | ((X14) = (X11))
% 0.21/0.60          | ((X13) != (k1_tarski @ X11)))),
% 0.21/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.60  thf('22', plain,
% 0.21/0.60      (![X11 : $i, X14 : $i]:
% 0.21/0.60         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.21/0.60      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.60  thf('23', plain,
% 0.21/0.60      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (sk_A)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['20', '22'])).
% 0.21/0.60  thf('24', plain, (((sk_B @ sk_C_1) = (sk_A))),
% 0.21/0.60      inference('sup-', [status(thm)], ['19', '23'])).
% 0.21/0.60  thf('25', plain,
% 0.21/0.60      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.21/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.60  thf('26', plain,
% 0.21/0.60      (((r2_hidden @ sk_A @ sk_C_1) | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.60      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.60  thf('27', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('28', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.21/0.60      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.21/0.60  thf(t38_zfmisc_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.60       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.21/0.60  thf('29', plain,
% 0.21/0.60      (![X49 : $i, X51 : $i, X52 : $i]:
% 0.21/0.60         ((r1_tarski @ (k2_tarski @ X49 @ X51) @ X52)
% 0.21/0.60          | ~ (r2_hidden @ X51 @ X52)
% 0.21/0.60          | ~ (r2_hidden @ X49 @ X52))),
% 0.21/0.60      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.60  thf('30', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X0 @ sk_C_1)
% 0.21/0.60          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_C_1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.60  thf('31', plain,
% 0.21/0.60      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.60        | (r1_tarski @ (k2_tarski @ (sk_B @ sk_C_1) @ sk_A) @ sk_C_1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['9', '30'])).
% 0.21/0.60  thf('32', plain, (((sk_B @ sk_C_1) = (sk_A))),
% 0.21/0.60      inference('sup-', [status(thm)], ['19', '23'])).
% 0.21/0.60  thf(t69_enumset1, axiom,
% 0.21/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.60  thf('33', plain,
% 0.21/0.60      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.21/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.60  thf('34', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.21/0.60      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.21/0.60  thf('35', plain,
% 0.21/0.60      ((((sk_C_1) = (k1_xboole_0)) | (r1_tarski @ sk_B_1 @ sk_C_1))),
% 0.21/0.60      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.21/0.60  thf('36', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('37', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.21/0.60      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.21/0.60  thf(t12_xboole_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.60  thf('38', plain,
% 0.21/0.60      (![X7 : $i, X8 : $i]:
% 0.21/0.60         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.21/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.60  thf('39', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.60  thf('40', plain, (((sk_B_1) = (sk_C_1))),
% 0.21/0.60      inference('sup+', [status(thm)], ['8', '39'])).
% 0.21/0.60  thf('41', plain, (((sk_B_1) != (sk_C_1))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('42', plain, ($false),
% 0.21/0.60      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.21/0.60  
% 0.21/0.60  % SZS output end Refutation
% 0.21/0.60  
% 0.21/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
