%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LWIpY4aLtt

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:45 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 104 expanded)
%              Number of leaves         :   17 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  303 ( 835 expanded)
%              Number of equality atoms :   50 ( 173 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X47: $i,X48: $i] :
      ( ( X48
        = ( k1_tarski @ X47 ) )
      | ( X48 = k1_xboole_0 )
      | ~ ( r1_tarski @ X48 @ ( k1_tarski @ X47 ) ) ) ),
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

thf('9',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','7'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
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

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','13'])).

thf('15',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,
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

thf('18',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( X14 = X11 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('19',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( sk_B @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('23',plain,(
    ! [X44: $i,X46: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X44 ) @ X46 )
      | ~ ( r2_hidden @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 )
      = sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('29',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
      = sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    sk_B_1 = sk_C_1 ),
    inference('sup+',[status(thm)],['8','31'])).

thf('33',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LWIpY4aLtt
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.59  % Solved by: fo/fo7.sh
% 0.37/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.59  % done 328 iterations in 0.141s
% 0.37/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.59  % SZS output start Refutation
% 0.37/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.59  thf(t44_zfmisc_1, conjecture,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.37/0.59          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.59          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.37/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.59        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.37/0.59             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.59             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.37/0.59    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.37/0.59  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(t7_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.59  thf('2', plain,
% 0.37/0.59      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.37/0.59      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.37/0.59  thf('3', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.37/0.59      inference('sup+', [status(thm)], ['1', '2'])).
% 0.37/0.59  thf(l3_zfmisc_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.37/0.59       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.37/0.59  thf('4', plain,
% 0.37/0.59      (![X47 : $i, X48 : $i]:
% 0.37/0.59         (((X48) = (k1_tarski @ X47))
% 0.37/0.59          | ((X48) = (k1_xboole_0))
% 0.37/0.59          | ~ (r1_tarski @ X48 @ (k1_tarski @ X47)))),
% 0.37/0.59      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.37/0.59  thf('5', plain,
% 0.37/0.59      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.59  thf('6', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('7', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.37/0.59      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.37/0.59  thf('8', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.37/0.59      inference('demod', [status(thm)], ['0', '7'])).
% 0.37/0.59  thf('9', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.37/0.59      inference('demod', [status(thm)], ['0', '7'])).
% 0.37/0.59  thf(t7_xboole_0, axiom,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.59          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.59  thf('10', plain,
% 0.37/0.59      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.37/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.59  thf(d3_xboole_0, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.37/0.59       ( ![D:$i]:
% 0.37/0.59         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.59           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.59  thf('11', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.59          | (r2_hidden @ X0 @ X2)
% 0.37/0.59          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.37/0.59  thf('12', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.37/0.59         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.37/0.59      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.59  thf('13', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (((X0) = (k1_xboole_0))
% 0.37/0.59          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['10', '12'])).
% 0.37/0.59  thf('14', plain,
% 0.37/0.59      (((r2_hidden @ (sk_B @ sk_C_1) @ sk_B_1) | ((sk_C_1) = (k1_xboole_0)))),
% 0.37/0.59      inference('sup+', [status(thm)], ['9', '13'])).
% 0.37/0.59  thf('15', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('16', plain, ((r2_hidden @ (sk_B @ sk_C_1) @ sk_B_1)),
% 0.37/0.59      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.37/0.59  thf('17', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.37/0.59      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.37/0.59  thf(d1_tarski, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.37/0.59  thf('18', plain,
% 0.37/0.59      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X14 @ X13)
% 0.37/0.59          | ((X14) = (X11))
% 0.37/0.59          | ((X13) != (k1_tarski @ X11)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d1_tarski])).
% 0.37/0.59  thf('19', plain,
% 0.37/0.59      (![X11 : $i, X14 : $i]:
% 0.37/0.59         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.37/0.59      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.59  thf('20', plain,
% 0.37/0.59      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (sk_A)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['17', '19'])).
% 0.37/0.59  thf('21', plain, (((sk_B @ sk_C_1) = (sk_A))),
% 0.37/0.59      inference('sup-', [status(thm)], ['16', '20'])).
% 0.37/0.59  thf('22', plain,
% 0.37/0.59      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.37/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.59  thf(l1_zfmisc_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.37/0.59  thf('23', plain,
% 0.37/0.59      (![X44 : $i, X46 : $i]:
% 0.37/0.59         ((r1_tarski @ (k1_tarski @ X44) @ X46) | ~ (r2_hidden @ X44 @ X46))),
% 0.37/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.37/0.59  thf('24', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.59  thf(t12_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.37/0.59  thf('25', plain,
% 0.37/0.59      (![X7 : $i, X8 : $i]:
% 0.37/0.59         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.37/0.59      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.37/0.59  thf('26', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (((X0) = (k1_xboole_0))
% 0.37/0.59          | ((k2_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0) = (X0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.59  thf('27', plain,
% 0.37/0.59      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1) = (sk_C_1))
% 0.37/0.59        | ((sk_C_1) = (k1_xboole_0)))),
% 0.37/0.59      inference('sup+', [status(thm)], ['21', '26'])).
% 0.37/0.59  thf('28', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.37/0.59      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.37/0.59  thf('29', plain,
% 0.37/0.59      ((((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))
% 0.37/0.59        | ((sk_C_1) = (k1_xboole_0)))),
% 0.37/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.37/0.59  thf('30', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('31', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 0.37/0.59      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.37/0.59  thf('32', plain, (((sk_B_1) = (sk_C_1))),
% 0.37/0.59      inference('sup+', [status(thm)], ['8', '31'])).
% 0.37/0.59  thf('33', plain, (((sk_B_1) != (sk_C_1))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('34', plain, ($false),
% 0.37/0.59      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.37/0.59  
% 0.37/0.59  % SZS output end Refutation
% 0.37/0.59  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
