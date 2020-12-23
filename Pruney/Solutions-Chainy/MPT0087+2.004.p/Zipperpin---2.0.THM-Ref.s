%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3yDe9FsCrc

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:32 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 168 expanded)
%              Number of leaves         :   17 (  61 expanded)
%              Depth                    :   16
%              Number of atoms          :  535 (1164 expanded)
%              Number of equality atoms :   61 ( 139 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t80_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t80_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k4_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k4_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['32','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ sk_B )
      = ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('45',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('46',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['11','55'])).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['0','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3yDe9FsCrc
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:13:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 164 iterations in 0.105s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(t80_xboole_1, conjecture,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.59        ( ( r1_xboole_0 @ A @ B ) =>
% 0.38/0.59          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t80_xboole_1])).
% 0.38/0.59  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(d7_xboole_0, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.38/0.59       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      (![X2 : $i, X3 : $i]:
% 0.38/0.59         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.38/0.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.38/0.59  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.59  thf(t51_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.38/0.59       ( A ) ))).
% 0.38/0.59  thf('4', plain,
% 0.38/0.59      (![X10 : $i, X11 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k4_xboole_0 @ X10 @ X11))
% 0.38/0.59           = (X10))),
% 0.38/0.59      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.38/0.59  thf('5', plain,
% 0.38/0.59      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.38/0.59      inference('sup+', [status(thm)], ['3', '4'])).
% 0.38/0.59  thf(commutativity_k2_xboole_0, axiom,
% 0.38/0.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.38/0.59  thf('6', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.59  thf(t1_boole, axiom,
% 0.38/0.59    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.59  thf('7', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.38/0.59      inference('cnf', [status(esa)], [t1_boole])).
% 0.38/0.59  thf('8', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.38/0.59  thf('9', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['5', '8'])).
% 0.38/0.59  thf(t52_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.38/0.59       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.38/0.59  thf('10', plain,
% 0.38/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 0.38/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 0.38/0.59              (k3_xboole_0 @ X12 @ X14)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.38/0.59  thf('11', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.38/0.59           = (k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.38/0.59  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.38/0.59  thf(t39_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.59  thf('13', plain,
% 0.38/0.59      (![X6 : $i, X7 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.38/0.59           = (k2_xboole_0 @ X6 @ X7))),
% 0.38/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.38/0.59  thf('14', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.59  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.38/0.59  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.59  thf(t48_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.59  thf('17', plain,
% 0.38/0.59      (![X8 : $i, X9 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.38/0.59           = (k3_xboole_0 @ X8 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.59  thf('18', plain,
% 0.38/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.38/0.59  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.59  thf(t79_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.38/0.59  thf('20', plain,
% 0.38/0.59      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 0.38/0.59      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.38/0.59  thf('21', plain,
% 0.38/0.59      (![X2 : $i, X3 : $i]:
% 0.38/0.59         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.38/0.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.38/0.59  thf('22', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.59  thf('23', plain,
% 0.38/0.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['19', '22'])).
% 0.38/0.59  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.59      inference('demod', [status(thm)], ['18', '23'])).
% 0.38/0.59  thf('25', plain,
% 0.38/0.59      (![X8 : $i, X9 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.38/0.59           = (k3_xboole_0 @ X8 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.59  thf('26', plain,
% 0.38/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['24', '25'])).
% 0.38/0.59  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.59  thf('28', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.59  thf('29', plain,
% 0.38/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 0.38/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 0.38/0.59              (k3_xboole_0 @ X12 @ X14)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.38/0.59  thf('30', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.38/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['28', '29'])).
% 0.38/0.59  thf('31', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.59  thf('32', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.38/0.59           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.38/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.38/0.59  thf('33', plain,
% 0.38/0.59      (![X8 : $i, X9 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.38/0.59           = (k3_xboole_0 @ X8 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.59  thf('34', plain,
% 0.38/0.59      (![X6 : $i, X7 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.38/0.59           = (k2_xboole_0 @ X6 @ X7))),
% 0.38/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.38/0.59  thf('35', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.38/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.38/0.59      inference('sup+', [status(thm)], ['33', '34'])).
% 0.38/0.59  thf('36', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.59  thf('37', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.59  thf('38', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.38/0.59           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.38/0.59      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.38/0.59  thf('39', plain,
% 0.38/0.59      (![X10 : $i, X11 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k4_xboole_0 @ X10 @ X11))
% 0.38/0.59           = (X10))),
% 0.38/0.59      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.38/0.59  thf('40', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 0.38/0.59      inference('sup+', [status(thm)], ['38', '39'])).
% 0.38/0.59  thf('41', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['32', '40'])).
% 0.38/0.59  thf('42', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.38/0.59           = (k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.38/0.59  thf('43', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ sk_A @ sk_B)
% 0.38/0.59           = (k2_xboole_0 @ sk_A @ 
% 0.38/0.59              (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))))),
% 0.38/0.59      inference('sup+', [status(thm)], ['41', '42'])).
% 0.38/0.59  thf('44', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['5', '8'])).
% 0.38/0.59  thf('45', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.59  thf('46', plain,
% 0.38/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 0.38/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 0.38/0.59              (k3_xboole_0 @ X12 @ X14)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.38/0.59  thf('47', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))
% 0.38/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ k1_xboole_0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['45', '46'])).
% 0.38/0.59  thf('48', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.59  thf('49', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.38/0.59  thf('50', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))
% 0.38/0.59           = (k4_xboole_0 @ sk_A @ X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.38/0.59  thf('51', plain,
% 0.38/0.59      (![X8 : $i, X9 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.38/0.59           = (k3_xboole_0 @ X8 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.59  thf('52', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 0.38/0.59           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['50', '51'])).
% 0.38/0.59  thf('53', plain,
% 0.38/0.59      (![X8 : $i, X9 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.38/0.59           = (k3_xboole_0 @ X8 @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.59  thf('54', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k3_xboole_0 @ sk_A @ X0)
% 0.38/0.59           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['52', '53'])).
% 0.38/0.59  thf('55', plain,
% 0.38/0.59      (![X0 : $i]: ((sk_A) = (k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.38/0.59      inference('demod', [status(thm)], ['43', '44', '54'])).
% 0.38/0.59  thf('56', plain,
% 0.38/0.59      (![X0 : $i]: ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) = (sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['11', '55'])).
% 0.38/0.59  thf('57', plain,
% 0.38/0.59      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 0.38/0.59      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.38/0.59  thf('58', plain,
% 0.38/0.59      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['56', '57'])).
% 0.38/0.59  thf('59', plain, ($false), inference('demod', [status(thm)], ['0', '58'])).
% 0.38/0.59  
% 0.38/0.59  % SZS output end Refutation
% 0.38/0.59  
% 0.38/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
