%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CsGPSHKZPd

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:37 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   59 (  73 expanded)
%              Number of leaves         :   15 (  28 expanded)
%              Depth                    :   16
%              Number of atoms          :  390 ( 494 expanded)
%              Number of equality atoms :   32 (  40 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t81_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k3_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X14 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('12',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('14',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','27'])).

thf('29',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['9','35'])).

thf('37',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('41',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['0','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CsGPSHKZPd
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 591 iterations in 0.227s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.67  thf(t81_xboole_1, conjecture,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.45/0.67       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.67        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.45/0.67          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 0.45/0.67  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(t79_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 0.45/0.67      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.45/0.67  thf(d7_xboole_0, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.45/0.67       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.67  thf('3', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.67  thf(t50_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.45/0.67       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.45/0.67  thf('4', plain,
% 0.45/0.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.68         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.45/0.68           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ 
% 0.45/0.68              (k3_xboole_0 @ X14 @ X16)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t50_xboole_1])).
% 0.45/0.68  thf(t49_xboole_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.45/0.68       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.45/0.68  thf('5', plain,
% 0.45/0.68      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.68         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.45/0.68           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.45/0.68      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.45/0.68  thf('6', plain,
% 0.45/0.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.68         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.45/0.68           = (k3_xboole_0 @ X14 @ 
% 0.45/0.68              (k4_xboole_0 @ X15 @ (k3_xboole_0 @ X14 @ X16))))),
% 0.45/0.68      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.68  thf('7', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0))
% 0.45/0.68           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.45/0.68              (k4_xboole_0 @ X2 @ k1_xboole_0)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['3', '6'])).
% 0.45/0.68  thf(t3_boole, axiom,
% 0.45/0.68    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.68  thf('8', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.45/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.68  thf('9', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0))
% 0.45/0.68           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 0.45/0.68      inference('demod', [status(thm)], ['7', '8'])).
% 0.45/0.68  thf('10', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(symmetry_r1_xboole_0, axiom,
% 0.45/0.68    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.45/0.68  thf('11', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i]:
% 0.45/0.68         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.45/0.68      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.45/0.68  thf('12', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.45/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.68  thf('13', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.68  thf('14', plain,
% 0.45/0.68      (((k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A) = (k1_xboole_0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.68  thf('15', plain,
% 0.45/0.68      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.68         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.45/0.68           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.45/0.68      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.45/0.68  thf('16', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ 
% 0.45/0.68           (k4_xboole_0 @ sk_A @ X0)) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['14', '15'])).
% 0.45/0.68  thf('17', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.45/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.68  thf('18', plain,
% 0.45/0.68      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 0.45/0.68      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.45/0.68  thf('19', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.45/0.68      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.68  thf('20', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i]:
% 0.45/0.68         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.45/0.68      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.45/0.68  thf('21', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.68  thf('22', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.68  thf('23', plain,
% 0.45/0.68      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.68  thf(t47_xboole_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.45/0.68  thf('24', plain,
% 0.45/0.68      (![X7 : $i, X8 : $i]:
% 0.45/0.68         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 0.45/0.68           = (k4_xboole_0 @ X7 @ X8))),
% 0.45/0.68      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.45/0.68  thf('25', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.45/0.68           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['23', '24'])).
% 0.45/0.68  thf('26', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.45/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.68  thf('27', plain,
% 0.45/0.68      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.68      inference('demod', [status(thm)], ['25', '26'])).
% 0.45/0.68  thf('28', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ 
% 0.45/0.68           (k4_xboole_0 @ sk_A @ X0)) = (k1_xboole_0))),
% 0.45/0.68      inference('demod', [status(thm)], ['16', '27'])).
% 0.45/0.68  thf('29', plain,
% 0.45/0.68      (![X0 : $i, X2 : $i]:
% 0.45/0.68         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.45/0.68      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.68  thf('30', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.68          | (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ 
% 0.45/0.68             (k4_xboole_0 @ sk_A @ X0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.68  thf('31', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ (k4_xboole_0 @ sk_A @ X0))),
% 0.45/0.68      inference('simplify', [status(thm)], ['30'])).
% 0.45/0.68  thf('32', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i]:
% 0.45/0.68         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.45/0.68      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.45/0.68  thf('33', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['31', '32'])).
% 0.45/0.68  thf('34', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.68  thf('35', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ 
% 0.45/0.68           (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.68  thf('36', plain,
% 0.45/0.68      (((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B) = (k1_xboole_0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['9', '35'])).
% 0.45/0.68  thf('37', plain,
% 0.45/0.68      (![X0 : $i, X2 : $i]:
% 0.45/0.68         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.45/0.68      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.68  thf('38', plain,
% 0.45/0.68      ((((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.68        | (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 0.45/0.68      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.68  thf('39', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.45/0.68      inference('simplify', [status(thm)], ['38'])).
% 0.45/0.68  thf('40', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i]:
% 0.45/0.68         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.45/0.68      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.45/0.68  thf('41', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['39', '40'])).
% 0.45/0.68  thf('42', plain, ($false), inference('demod', [status(thm)], ['0', '41'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.45/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
