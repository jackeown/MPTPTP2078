%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JTGG1Iu9SH

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:43 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 308 expanded)
%              Number of leaves         :   12 (  97 expanded)
%              Depth                    :   16
%              Number of atoms          :  545 (3523 expanded)
%              Number of equality atoms :   92 ( 490 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('5',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t37_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
       != ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) )
      | ( X12 = X15 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( X0 = sk_B )
      | ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( X0 = sk_B )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = sk_B ) ),
    inference(eq_res,[status(thm)],['12'])).

thf('14',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('23',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('25',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('26',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','26'])).

thf(t38_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_zfmisc_1 @ A @ A @ A )
        = ( k3_zfmisc_1 @ B @ B @ B ) )
     => ( A = B ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17 = X16 )
      | ( ( k3_zfmisc_1 @ X17 @ X17 @ X17 )
       != ( k3_zfmisc_1 @ X16 @ X16 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t38_mcart_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ X0 @ X0 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['23','29'])).

thf('31',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('32',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf('35',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = sk_B )
    | ( sk_A = sk_B ) ),
    inference(demod,[status(thm)],['20','33','34'])).

thf('36',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ X0 @ X0 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('39',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf('40',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ X0 @ X0 @ X0 )
       != sk_B )
      | ( X0 = sk_B ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( sk_B != sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JTGG1Iu9SH
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:18:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.52  % Solved by: fo/fo7.sh
% 0.36/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.52  % done 105 iterations in 0.069s
% 0.36/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.52  % SZS output start Refutation
% 0.36/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.52  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.36/0.52  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.36/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.52  thf(d3_zfmisc_1, axiom,
% 0.36/0.52    (![A:$i,B:$i,C:$i]:
% 0.36/0.52     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.36/0.52       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.36/0.52  thf('0', plain,
% 0.36/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.52         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.36/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.36/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.52  thf('1', plain,
% 0.36/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.52         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.36/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.36/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.52  thf('2', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.52         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.36/0.52           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.36/0.52      inference('sup+', [status(thm)], ['0', '1'])).
% 0.36/0.52  thf(d4_zfmisc_1, axiom,
% 0.36/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.52     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.36/0.52       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.36/0.52  thf('3', plain,
% 0.36/0.52      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.52         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.36/0.52           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.36/0.52      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.36/0.52  thf('4', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.52         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.36/0.52           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.36/0.52      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.52  thf(t58_mcart_1, conjecture,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.36/0.52       ( ( A ) = ( B ) ) ))).
% 0.36/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.52    (~( ![A:$i,B:$i]:
% 0.36/0.52        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.36/0.52          ( ( A ) = ( B ) ) ) )),
% 0.36/0.52    inference('cnf.neg', [status(esa)], [t58_mcart_1])).
% 0.36/0.52  thf('5', plain,
% 0.36/0.52      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.36/0.52         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('6', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.52         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.36/0.52           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.36/0.52      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.52  thf(t37_mcart_1, axiom,
% 0.36/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.52     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.36/0.52       ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 0.36/0.52         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.36/0.52  thf('7', plain,
% 0.36/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.52         (((k3_zfmisc_1 @ X10 @ X11 @ X12) = (k1_xboole_0))
% 0.36/0.52          | ((k3_zfmisc_1 @ X10 @ X11 @ X12) != (k3_zfmisc_1 @ X13 @ X14 @ X15))
% 0.36/0.52          | ((X12) = (X15)))),
% 0.36/0.52      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.36/0.52  thf('8', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.52         (((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.36/0.52          | ((X4) = (X0))
% 0.36/0.52          | ((k3_zfmisc_1 @ X6 @ X5 @ X4) = (k1_xboole_0)))),
% 0.36/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.52  thf('9', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.52         (((k3_zfmisc_1 @ X2 @ X1 @ X0)
% 0.36/0.52            != (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.36/0.52          | ((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 0.36/0.52          | ((X0) = (sk_B)))),
% 0.36/0.52      inference('sup-', [status(thm)], ['5', '8'])).
% 0.36/0.52  thf('10', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.52         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.52            != (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.36/0.52          | ((X0) = (sk_B))
% 0.36/0.52          | ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0) = (k1_xboole_0)))),
% 0.36/0.52      inference('sup-', [status(thm)], ['4', '9'])).
% 0.36/0.52  thf('11', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.52         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.36/0.52           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.36/0.52      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.52  thf('12', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.52         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.52            != (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.36/0.52          | ((X0) = (sk_B))
% 0.36/0.52          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.36/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.52  thf('13', plain,
% 0.36/0.52      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.36/0.52        | ((sk_A) = (sk_B)))),
% 0.36/0.52      inference('eq_res', [status(thm)], ['12'])).
% 0.36/0.52  thf('14', plain, (((sk_A) != (sk_B))),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('15', plain,
% 0.36/0.52      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.36/0.52      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.36/0.52  thf('16', plain,
% 0.36/0.52      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.52         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.36/0.52           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.36/0.52      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.36/0.52  thf(t113_zfmisc_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.52  thf('17', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         (((X0) = (k1_xboole_0))
% 0.36/0.52          | ((X1) = (k1_xboole_0))
% 0.36/0.52          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.36/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.52  thf('18', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.52         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.36/0.52          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0))
% 0.36/0.52          | ((X0) = (k1_xboole_0)))),
% 0.36/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.52  thf('19', plain,
% 0.36/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.52        | ((sk_A) = (k1_xboole_0))
% 0.36/0.52        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.36/0.52      inference('sup-', [status(thm)], ['15', '18'])).
% 0.36/0.52  thf('20', plain,
% 0.36/0.52      ((((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.36/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.36/0.52      inference('simplify', [status(thm)], ['19'])).
% 0.36/0.52  thf('21', plain,
% 0.36/0.52      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.36/0.52         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('22', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.52         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.36/0.52          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0))
% 0.36/0.52          | ((X0) = (k1_xboole_0)))),
% 0.36/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.52  thf('23', plain,
% 0.36/0.52      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0))
% 0.36/0.52        | ((sk_B) = (k1_xboole_0))
% 0.36/0.52        | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (k1_xboole_0)))),
% 0.36/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.52  thf('24', plain,
% 0.36/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.52         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.36/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.36/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.53  thf('25', plain,
% 0.36/0.53      (![X1 : $i, X2 : $i]:
% 0.36/0.53         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.36/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.53  thf('26', plain,
% 0.36/0.53      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.53      inference('simplify', [status(thm)], ['25'])).
% 0.36/0.53  thf('27', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]:
% 0.36/0.53         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.53      inference('sup+', [status(thm)], ['24', '26'])).
% 0.36/0.53  thf(t38_mcart_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( ( k3_zfmisc_1 @ A @ A @ A ) = ( k3_zfmisc_1 @ B @ B @ B ) ) =>
% 0.36/0.53       ( ( A ) = ( B ) ) ))).
% 0.36/0.53  thf('28', plain,
% 0.36/0.53      (![X16 : $i, X17 : $i]:
% 0.36/0.53         (((X17) = (X16))
% 0.36/0.53          | ((k3_zfmisc_1 @ X17 @ X17 @ X17) != (k3_zfmisc_1 @ X16 @ X16 @ X16)))),
% 0.36/0.53      inference('cnf', [status(esa)], [t38_mcart_1])).
% 0.36/0.53  thf('29', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (((k3_zfmisc_1 @ X0 @ X0 @ X0) != (k1_xboole_0))
% 0.36/0.53          | ((X0) = (k1_xboole_0)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.53  thf('30', plain,
% 0.36/0.53      ((((sk_B) = (k1_xboole_0))
% 0.36/0.53        | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0)))),
% 0.36/0.53      inference('clc', [status(thm)], ['23', '29'])).
% 0.36/0.53  thf('31', plain,
% 0.36/0.53      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.36/0.53      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.36/0.53  thf('32', plain,
% 0.36/0.53      ((((sk_B) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.36/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.36/0.53  thf('33', plain, (((sk_B) = (k1_xboole_0))),
% 0.36/0.53      inference('simplify', [status(thm)], ['32'])).
% 0.36/0.53  thf('34', plain, (((sk_B) = (k1_xboole_0))),
% 0.36/0.53      inference('simplify', [status(thm)], ['32'])).
% 0.36/0.53  thf('35', plain,
% 0.36/0.53      ((((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.36/0.53      inference('demod', [status(thm)], ['20', '33', '34'])).
% 0.36/0.53  thf('36', plain, (((sk_A) != (sk_B))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('37', plain, (((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (sk_B))),
% 0.36/0.53      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.36/0.53  thf('38', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (((k3_zfmisc_1 @ X0 @ X0 @ X0) != (k1_xboole_0))
% 0.36/0.53          | ((X0) = (k1_xboole_0)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.53  thf('39', plain, (((sk_B) = (k1_xboole_0))),
% 0.36/0.53      inference('simplify', [status(thm)], ['32'])).
% 0.36/0.53  thf('40', plain, (((sk_B) = (k1_xboole_0))),
% 0.36/0.53      inference('simplify', [status(thm)], ['32'])).
% 0.36/0.53  thf('41', plain,
% 0.36/0.53      (![X0 : $i]: (((k3_zfmisc_1 @ X0 @ X0 @ X0) != (sk_B)) | ((X0) = (sk_B)))),
% 0.36/0.53      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.36/0.53  thf('42', plain, ((((sk_B) != (sk_B)) | ((sk_A) = (sk_B)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['37', '41'])).
% 0.36/0.53  thf('43', plain, (((sk_A) = (sk_B))),
% 0.36/0.53      inference('simplify', [status(thm)], ['42'])).
% 0.36/0.53  thf('44', plain, (((sk_A) != (sk_B))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('45', plain, ($false),
% 0.36/0.53      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.36/0.53  
% 0.36/0.53  % SZS output end Refutation
% 0.36/0.53  
% 0.36/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
