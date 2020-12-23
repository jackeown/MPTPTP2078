%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uv68uTraFw

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 219 expanded)
%              Number of leaves         :   10 (  61 expanded)
%              Depth                    :   20
%              Number of atoms          :  508 (2721 expanded)
%              Number of equality atoms :  117 ( 580 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t38_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_zfmisc_1 @ A @ A @ A )
        = ( k3_zfmisc_1 @ B @ B @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_zfmisc_1 @ A @ A @ A )
          = ( k3_zfmisc_1 @ B @ B @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t38_mcart_1])).

thf('0',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
    = ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
       != k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('2',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
    = ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t134_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X4
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A ) )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = ( k2_zfmisc_1 @ sk_B @ sk_B ) )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ),
    inference(eq_res,[status(thm)],['10'])).

thf('12',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ),
    inference(eq_res,[status(thm)],['10'])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_A @ sk_A )
       != ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = X1 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( sk_B = X1 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
       != ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['15'])).

thf('17',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('20',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('23',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf('25',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','24'])).

thf('26',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('31',plain,
    ( ( sk_B = sk_A )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
     != sk_A ) ),
    inference(demod,[status(thm)],['3','29','30'])).

thf('32',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
 != sk_A ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( X10 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X10 @ X11 @ X13 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('35',plain,(
    ! [X11: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X11 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('37',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('38',plain,(
    ! [X11: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ sk_A @ X11 @ X13 )
      = sk_A ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,(
    $false ),
    inference(simplify,[status(thm)],['39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uv68uTraFw
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 55 iterations in 0.039s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(t38_mcart_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k3_zfmisc_1 @ A @ A @ A ) = ( k3_zfmisc_1 @ B @ B @ B ) ) =>
% 0.20/0.49       ( ( A ) = ( B ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( ( k3_zfmisc_1 @ A @ A @ A ) = ( k3_zfmisc_1 @ B @ B @ B ) ) =>
% 0.20/0.49          ( ( A ) = ( B ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t38_mcart_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k3_zfmisc_1 @ sk_B @ sk_B @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t35_mcart_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.20/0.49       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         (((k3_zfmisc_1 @ X10 @ X11 @ X12) != (k1_xboole_0))
% 0.20/0.49          | ((X12) = (k1_xboole_0))
% 0.20/0.49          | ((X11) = (k1_xboole_0))
% 0.20/0.49          | ((X10) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      ((((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) != (k1_xboole_0))
% 0.20/0.49        | ((sk_B) = (k1_xboole_0))
% 0.20/0.49        | ((sk_B) = (k1_xboole_0))
% 0.20/0.49        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      ((((sk_B) = (k1_xboole_0))
% 0.20/0.49        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) != (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.49  thf(d3_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.49       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.20/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k3_zfmisc_1 @ sk_B @ sk_B @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.20/0.49           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.49  thf(t134_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.20/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.49         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         (((X3) = (k1_xboole_0))
% 0.20/0.49          | ((X4) = (k1_xboole_0))
% 0.20/0.49          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 0.20/0.49          | ((X4) = (X5)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         (((k2_zfmisc_1 @ X4 @ X3) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.49          | ((X4) = (k2_zfmisc_1 @ X2 @ X1))
% 0.20/0.49          | ((X4) = (k1_xboole_0))
% 0.20/0.49          | ((X3) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k2_zfmisc_1 @ X1 @ X0) != (k3_zfmisc_1 @ sk_A @ sk_A @ sk_A))
% 0.20/0.49          | ((X0) = (k1_xboole_0))
% 0.20/0.49          | ((X1) = (k1_xboole_0))
% 0.20/0.49          | ((X1) = (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ sk_A @ sk_A @ sk_A))
% 0.20/0.49          | ((k2_zfmisc_1 @ X2 @ X1) = (k2_zfmisc_1 @ sk_B @ sk_B))
% 0.20/0.49          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.20/0.49          | ((X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((((sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.20/0.49      inference('eq_res', [status(thm)], ['10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      ((((sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.20/0.49      inference('eq_res', [status(thm)], ['10'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         (((X3) = (k1_xboole_0))
% 0.20/0.49          | ((X4) = (k1_xboole_0))
% 0.20/0.49          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 0.20/0.49          | ((X4) = (X5)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k2_zfmisc_1 @ sk_A @ sk_A) != (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.49          | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.49          | ((sk_A) = (k1_xboole_0))
% 0.20/0.49          | ((sk_B) = (X1))
% 0.20/0.49          | ((sk_B) = (k1_xboole_0))
% 0.20/0.49          | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((sk_B) = (k1_xboole_0))
% 0.20/0.49          | ((sk_B) = (X1))
% 0.20/0.49          | ((sk_A) = (k1_xboole_0))
% 0.20/0.49          | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.49          | ((k2_zfmisc_1 @ sk_A @ sk_A) != (k2_zfmisc_1 @ X1 @ X0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((sk_B) = (sk_A))
% 0.20/0.49        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.49      inference('eq_res', [status(thm)], ['15'])).
% 0.20/0.49  thf('17', plain, (((sk_A) != (sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      ((((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf(t113_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((X0) = (k1_xboole_0))
% 0.20/0.49          | ((X1) = (k1_xboole_0))
% 0.20/0.49          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49        | ((sk_B) = (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i]:
% 0.20/0.49         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.20/0.49          | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['21', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      ((((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['11', '24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      ((((sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((X0) = (k1_xboole_0))
% 0.20/0.49          | ((X1) = (k1_xboole_0))
% 0.20/0.49          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.49  thf('30', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      ((((sk_B) = (sk_A)) | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) != (sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['3', '29', '30'])).
% 0.20/0.49  thf('32', plain, (((sk_A) != (sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('33', plain, (((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) != (sk_A))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.20/0.49         (((X10) != (k1_xboole_0))
% 0.20/0.49          | ((k3_zfmisc_1 @ X10 @ X11 @ X13) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X11 : $i, X13 : $i]:
% 0.20/0.49         ((k3_zfmisc_1 @ k1_xboole_0 @ X11 @ X13) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.49  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.49  thf('37', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X11 : $i, X13 : $i]: ((k3_zfmisc_1 @ sk_A @ X11 @ X13) = (sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.20/0.49  thf('39', plain, (((sk_A) != (sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['33', '38'])).
% 0.20/0.49  thf('40', plain, ($false), inference('simplify', [status(thm)], ['39'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
