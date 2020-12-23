%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4zRhGJHk3B

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:42 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 239 expanded)
%              Number of leaves         :   12 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :  583 (3011 expanded)
%              Number of equality atoms :  113 ( 566 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(t58_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
        = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
          = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_mcart_1])).

thf('0',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_zfmisc_1 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('13',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t134_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ( X3 = X6 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( X0 = sk_B )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = sk_B ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('20',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('23',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['23'])).

thf('26',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['23'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != sk_A )
      | ( X0 = sk_A )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['11','24','25','26'])).

thf('28',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != sk_A )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['0','27'])).

thf('29',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != sk_A )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('32',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('33',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','33'])).

thf('35',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['23'])).

thf('36',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['23'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( sk_A != sk_A )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['30','37'])).

thf('39',plain,
    ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
    = sk_A ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('41',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['23'])).

thf('42',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['23'])).

thf('43',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['23'])).

thf('44',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['23'])).

thf('45',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
       != sk_A )
      | ( X16 = sk_A )
      | ( X15 = sk_A )
      | ( X14 = sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,
    ( ( sk_A != sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4zRhGJHk3B
% 0.14/0.36  % Computer   : n001.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 18:54:30 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 108 iterations in 0.050s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.50  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.23/0.50  thf(t58_mcart_1, conjecture,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.23/0.50       ( ( A ) = ( B ) ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i,B:$i]:
% 0.23/0.50        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.23/0.50          ( ( A ) = ( B ) ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t58_mcart_1])).
% 0.23/0.50  thf('0', plain,
% 0.23/0.50      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.23/0.50         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(d3_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.23/0.50       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.50         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.23/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.23/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.50         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.23/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.23/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.50         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.23/0.50           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.23/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.23/0.50  thf(d4_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.50     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.23/0.50       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.23/0.50  thf('4', plain,
% 0.23/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.50         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.23/0.50           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.23/0.50      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.23/0.50  thf('5', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.50         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.23/0.50           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.23/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.50         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.23/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.23/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.23/0.50  thf(t113_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.23/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.23/0.50  thf('7', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (((X0) = (k1_xboole_0))
% 0.23/0.50          | ((X1) = (k1_xboole_0))
% 0.23/0.50          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.23/0.50  thf('8', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.50         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.23/0.50          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.23/0.50          | ((X0) = (k1_xboole_0)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.50  thf('9', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.50         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.23/0.50          | ((X0) = (k1_xboole_0))
% 0.23/0.50          | ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1) = (k1_xboole_0)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['5', '8'])).
% 0.23/0.50  thf('10', plain,
% 0.23/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.50         ((k3_zfmisc_1 @ X7 @ X8 @ X9)
% 0.23/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9))),
% 0.23/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.23/0.50  thf('11', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.50         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.23/0.50          | ((X0) = (k1_xboole_0))
% 0.23/0.50          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 0.23/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.50         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.23/0.50           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.23/0.50      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.23/0.50  thf('13', plain,
% 0.23/0.50      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.23/0.50         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('14', plain,
% 0.23/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.50         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.23/0.50           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.23/0.50      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.23/0.50  thf(t134_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.23/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.23/0.50         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 0.23/0.50  thf('15', plain,
% 0.23/0.50      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.50         (((X3) = (k1_xboole_0))
% 0.23/0.50          | ((X4) = (k1_xboole_0))
% 0.23/0.50          | ((k2_zfmisc_1 @ X4 @ X3) != (k2_zfmisc_1 @ X5 @ X6))
% 0.23/0.50          | ((X3) = (X6)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.23/0.50  thf('16', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.50         (((k2_zfmisc_1 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.23/0.50          | ((X4) = (X0))
% 0.23/0.50          | ((X5) = (k1_xboole_0))
% 0.23/0.50          | ((X4) = (k1_xboole_0)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.50  thf('17', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (((k2_zfmisc_1 @ X1 @ X0) != (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.23/0.50          | ((X0) = (k1_xboole_0))
% 0.23/0.50          | ((X1) = (k1_xboole_0))
% 0.23/0.50          | ((X0) = (sk_B)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['13', '16'])).
% 0.23/0.50  thf('18', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.50         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.23/0.50            != (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.23/0.50          | ((X0) = (sk_B))
% 0.23/0.50          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0))
% 0.23/0.50          | ((X0) = (k1_xboole_0)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['12', '17'])).
% 0.23/0.50  thf('19', plain,
% 0.23/0.50      ((((sk_A) = (k1_xboole_0))
% 0.23/0.50        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.23/0.50        | ((sk_A) = (sk_B)))),
% 0.23/0.50      inference('eq_res', [status(thm)], ['18'])).
% 0.23/0.50  thf('20', plain, (((sk_A) != (sk_B))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('21', plain,
% 0.23/0.50      ((((sk_A) = (k1_xboole_0))
% 0.23/0.50        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.23/0.50      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.23/0.50  thf(t35_mcart_1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.23/0.50         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.23/0.50       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.23/0.50  thf('22', plain,
% 0.23/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.50         (((k3_zfmisc_1 @ X14 @ X15 @ X16) != (k1_xboole_0))
% 0.23/0.50          | ((X16) = (k1_xboole_0))
% 0.23/0.50          | ((X15) = (k1_xboole_0))
% 0.23/0.50          | ((X14) = (k1_xboole_0)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.23/0.50  thf('23', plain,
% 0.23/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.23/0.50        | ((sk_A) = (k1_xboole_0))
% 0.23/0.50        | ((sk_A) = (k1_xboole_0))
% 0.23/0.50        | ((sk_A) = (k1_xboole_0))
% 0.23/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.23/0.50  thf('24', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.23/0.50  thf('25', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.23/0.50  thf('26', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.23/0.50  thf('27', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.50         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (sk_A))
% 0.23/0.50          | ((X0) = (sk_A))
% 0.23/0.50          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (sk_A)))),
% 0.23/0.50      inference('demod', [status(thm)], ['11', '24', '25', '26'])).
% 0.23/0.50  thf('28', plain,
% 0.23/0.50      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (sk_A))
% 0.23/0.50        | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (sk_A))
% 0.23/0.50        | ((sk_B) = (sk_A)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['0', '27'])).
% 0.23/0.50  thf('29', plain, (((sk_A) != (sk_B))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('30', plain,
% 0.23/0.50      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (sk_A))
% 0.23/0.50        | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (sk_A)))),
% 0.23/0.50      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.23/0.50  thf('31', plain,
% 0.23/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.50         ((k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)
% 0.23/0.50           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X10 @ X11 @ X12) @ X13))),
% 0.23/0.50      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.23/0.50  thf('32', plain,
% 0.23/0.50      (![X1 : $i, X2 : $i]:
% 0.23/0.50         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.23/0.50  thf('33', plain,
% 0.23/0.50      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['32'])).
% 0.23/0.50  thf('34', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.50         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.50      inference('sup+', [status(thm)], ['31', '33'])).
% 0.23/0.50  thf('35', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.23/0.50  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.51      inference('simplify', [status(thm)], ['23'])).
% 0.23/0.51  thf('37', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.51         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_A) = (sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.23/0.51  thf('38', plain,
% 0.23/0.51      ((((sk_A) != (sk_A)) | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (sk_A)))),
% 0.23/0.51      inference('demod', [status(thm)], ['30', '37'])).
% 0.23/0.51  thf('39', plain, (((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (sk_A))),
% 0.23/0.51      inference('simplify', [status(thm)], ['38'])).
% 0.23/0.51  thf('40', plain,
% 0.23/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.51         (((k3_zfmisc_1 @ X14 @ X15 @ X16) != (k1_xboole_0))
% 0.23/0.51          | ((X16) = (k1_xboole_0))
% 0.23/0.51          | ((X15) = (k1_xboole_0))
% 0.23/0.51          | ((X14) = (k1_xboole_0)))),
% 0.23/0.51      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.23/0.51  thf('41', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.51      inference('simplify', [status(thm)], ['23'])).
% 0.23/0.51  thf('42', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.51      inference('simplify', [status(thm)], ['23'])).
% 0.23/0.51  thf('43', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.51      inference('simplify', [status(thm)], ['23'])).
% 0.23/0.51  thf('44', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.51      inference('simplify', [status(thm)], ['23'])).
% 0.23/0.51  thf('45', plain,
% 0.23/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.51         (((k3_zfmisc_1 @ X14 @ X15 @ X16) != (sk_A))
% 0.23/0.51          | ((X16) = (sk_A))
% 0.23/0.51          | ((X15) = (sk_A))
% 0.23/0.51          | ((X14) = (sk_A)))),
% 0.23/0.51      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 0.23/0.51  thf('46', plain,
% 0.23/0.51      ((((sk_A) != (sk_A))
% 0.23/0.51        | ((sk_B) = (sk_A))
% 0.23/0.51        | ((sk_B) = (sk_A))
% 0.23/0.51        | ((sk_B) = (sk_A)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['39', '45'])).
% 0.23/0.51  thf('47', plain, (((sk_B) = (sk_A))),
% 0.23/0.51      inference('simplify', [status(thm)], ['46'])).
% 0.23/0.51  thf('48', plain, (((sk_A) != (sk_B))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('49', plain, ($false),
% 0.23/0.51      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
