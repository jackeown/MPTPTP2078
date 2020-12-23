%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9Lkvj7C7yj

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:23 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   65 (  85 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :   19
%              Number of atoms          :  405 ( 580 expanded)
%              Number of equality atoms :   42 (  57 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t77_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('7',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('10',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('16',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('19',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['7','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('44',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['35','44'])).

thf('46',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9Lkvj7C7yj
% 0.15/0.37  % Computer   : n013.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 20:21:25 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.38/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.55  % Solved by: fo/fo7.sh
% 0.38/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.55  % done 118 iterations in 0.062s
% 0.38/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.55  % SZS output start Refutation
% 0.38/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.55  thf(t77_xboole_1, conjecture,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.38/0.55          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.55        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.38/0.55             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.38/0.55    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.38/0.55  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('1', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(l32_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.55  thf('2', plain,
% 0.38/0.55      (![X5 : $i, X7 : $i]:
% 0.38/0.55         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.38/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.55  thf('3', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.55  thf(t48_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.55  thf('4', plain,
% 0.38/0.55      (![X15 : $i, X16 : $i]:
% 0.38/0.55         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.38/0.55           = (k3_xboole_0 @ X15 @ X16))),
% 0.38/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.55  thf('5', plain,
% 0.38/0.55      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.38/0.55      inference('sup+', [status(thm)], ['3', '4'])).
% 0.38/0.55  thf(t3_boole, axiom,
% 0.38/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.55  thf('6', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.55  thf('7', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.38/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.38/0.55  thf('8', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(symmetry_r1_xboole_0, axiom,
% 0.38/0.55    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.38/0.55  thf('9', plain,
% 0.38/0.55      (![X3 : $i, X4 : $i]:
% 0.38/0.55         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.38/0.55      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.38/0.55  thf('10', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.38/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.55  thf(d7_xboole_0, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.38/0.55       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.55  thf('11', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.38/0.55  thf('12', plain,
% 0.38/0.55      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A) = (k1_xboole_0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.55  thf(t16_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.38/0.55       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.38/0.55  thf('13', plain,
% 0.38/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.55         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 0.38/0.55           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.38/0.55  thf('14', plain,
% 0.38/0.55      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ sk_A)) = (k1_xboole_0))),
% 0.38/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.55  thf('15', plain,
% 0.38/0.55      (![X0 : $i, X2 : $i]:
% 0.38/0.55         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.38/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.38/0.55  thf('16', plain,
% 0.38/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.55        | (r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ sk_A)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.55  thf('17', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ sk_A))),
% 0.38/0.55      inference('simplify', [status(thm)], ['16'])).
% 0.38/0.55  thf('18', plain,
% 0.38/0.55      (![X3 : $i, X4 : $i]:
% 0.38/0.55         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.38/0.55      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.38/0.55  thf('19', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_B)),
% 0.38/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.55  thf('20', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.38/0.55  thf('21', plain,
% 0.38/0.55      (((k3_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.55  thf('22', plain,
% 0.38/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.55         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 0.38/0.55           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.38/0.55  thf('23', plain,
% 0.38/0.55      (((k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.38/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.55  thf('24', plain,
% 0.38/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.55         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 0.38/0.55           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.38/0.55  thf('25', plain,
% 0.38/0.55      (![X0 : $i, X2 : $i]:
% 0.38/0.55         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.38/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.38/0.55  thf('26', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.38/0.55          | (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.55  thf('27', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (((k3_xboole_0 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 0.38/0.55          | (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 0.38/0.55             (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['23', '26'])).
% 0.38/0.55  thf(t2_boole, axiom,
% 0.38/0.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.38/0.55  thf('28', plain,
% 0.38/0.55      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.38/0.55  thf('29', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.55          | (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 0.38/0.55             (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.38/0.55      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.55  thf('30', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C) @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.38/0.55  thf('31', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.55      inference('sup+', [status(thm)], ['7', '30'])).
% 0.38/0.55  thf('32', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.38/0.55  thf('33', plain,
% 0.38/0.55      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.55  thf('34', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.38/0.55          | (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.55  thf('35', plain,
% 0.38/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.55        | (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_A) @ sk_B))),
% 0.38/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.55  thf('36', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.55  thf('37', plain,
% 0.38/0.55      (![X15 : $i, X16 : $i]:
% 0.38/0.55         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.38/0.55           = (k3_xboole_0 @ X15 @ X16))),
% 0.38/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.55  thf('38', plain,
% 0.38/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.55      inference('sup+', [status(thm)], ['36', '37'])).
% 0.38/0.55  thf('39', plain,
% 0.38/0.55      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.38/0.55  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.55      inference('demod', [status(thm)], ['38', '39'])).
% 0.38/0.55  thf('41', plain,
% 0.38/0.55      (![X15 : $i, X16 : $i]:
% 0.38/0.55         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.38/0.55           = (k3_xboole_0 @ X15 @ X16))),
% 0.38/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.55  thf('42', plain,
% 0.38/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.38/0.55      inference('sup+', [status(thm)], ['40', '41'])).
% 0.38/0.55  thf('43', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.55  thf('44', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.38/0.55      inference('demod', [status(thm)], ['42', '43'])).
% 0.38/0.55  thf('45', plain,
% 0.38/0.55      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.55      inference('demod', [status(thm)], ['35', '44'])).
% 0.38/0.55  thf('46', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.38/0.55      inference('simplify', [status(thm)], ['45'])).
% 0.38/0.55  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
