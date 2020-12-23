%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w8pVMIiCjX

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:33 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 140 expanded)
%              Number of leaves         :   18 (  50 expanded)
%              Depth                    :   20
%              Number of atoms          :  480 ( 959 expanded)
%              Number of equality atoms :   49 (  86 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','12'])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['4','7'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = ( k5_xboole_0 @ sk_C @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k5_xboole_0 @ sk_C @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = sk_C ) ),
    inference('sup+',[status(thm)],['15','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_C )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['14','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('53',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('54',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['51','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['13','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w8pVMIiCjX
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.69  % Solved by: fo/fo7.sh
% 0.48/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.69  % done 912 iterations in 0.242s
% 0.48/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.69  % SZS output start Refutation
% 0.48/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.48/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.48/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.48/0.69  thf(t106_xboole_1, conjecture,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.48/0.69       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.48/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.69    (~( ![A:$i,B:$i,C:$i]:
% 0.48/0.69        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.48/0.69          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.48/0.69    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.48/0.69  thf('0', plain,
% 0.48/0.69      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('1', plain,
% 0.48/0.69      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.48/0.69      inference('split', [status(esa)], ['0'])).
% 0.48/0.69  thf('2', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf(t28_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.48/0.69  thf('3', plain,
% 0.48/0.69      (![X10 : $i, X11 : $i]:
% 0.48/0.69         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.48/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.48/0.69  thf('4', plain,
% 0.48/0.69      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.48/0.69      inference('sup-', [status(thm)], ['2', '3'])).
% 0.48/0.69  thf(t49_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.48/0.69       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.48/0.69  thf('5', plain,
% 0.48/0.69      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.48/0.69         ((k3_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 0.48/0.69           = (k4_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14))),
% 0.48/0.69      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.48/0.69  thf(t79_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.48/0.69  thf('6', plain,
% 0.48/0.69      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.48/0.69      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.48/0.69  thf('7', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 0.48/0.69      inference('sup+', [status(thm)], ['5', '6'])).
% 0.48/0.69  thf('8', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.48/0.69      inference('sup+', [status(thm)], ['4', '7'])).
% 0.48/0.69  thf('9', plain,
% 0.48/0.69      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.48/0.69      inference('split', [status(esa)], ['0'])).
% 0.48/0.69  thf('10', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.48/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.48/0.69  thf('11', plain,
% 0.48/0.69      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.48/0.69      inference('split', [status(esa)], ['0'])).
% 0.48/0.69  thf('12', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.48/0.69      inference('sat_resolution*', [status(thm)], ['10', '11'])).
% 0.48/0.69  thf('13', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.48/0.69      inference('simpl_trail', [status(thm)], ['1', '12'])).
% 0.48/0.69  thf('14', plain,
% 0.48/0.69      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.48/0.69      inference('sup-', [status(thm)], ['2', '3'])).
% 0.48/0.69  thf(commutativity_k3_xboole_0, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.48/0.69  thf('15', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.69  thf('16', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.48/0.69      inference('sup+', [status(thm)], ['4', '7'])).
% 0.48/0.69  thf(d7_xboole_0, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.48/0.69       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.48/0.69  thf('17', plain,
% 0.48/0.70      (![X2 : $i, X3 : $i]:
% 0.48/0.70         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.48/0.70      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.48/0.70  thf('18', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.70  thf('19', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.70  thf('20', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.48/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.48/0.70  thf(t100_xboole_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.48/0.70  thf('21', plain,
% 0.48/0.70      (![X8 : $i, X9 : $i]:
% 0.48/0.70         ((k4_xboole_0 @ X8 @ X9)
% 0.48/0.70           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.70  thf('22', plain,
% 0.48/0.70      (((k4_xboole_0 @ sk_C @ sk_A) = (k5_xboole_0 @ sk_C @ k1_xboole_0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['20', '21'])).
% 0.48/0.70  thf(t5_boole, axiom,
% 0.48/0.70    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.48/0.70  thf('23', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.48/0.70      inference('cnf', [status(esa)], [t5_boole])).
% 0.48/0.70  thf('24', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.48/0.70      inference('demod', [status(thm)], ['22', '23'])).
% 0.48/0.70  thf('25', plain,
% 0.48/0.70      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.48/0.70      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.48/0.70  thf('26', plain,
% 0.48/0.70      (![X2 : $i, X3 : $i]:
% 0.48/0.70         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.48/0.70      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.48/0.70  thf('27', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['25', '26'])).
% 0.48/0.70  thf('28', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.70  thf('29', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.48/0.70      inference('demod', [status(thm)], ['27', '28'])).
% 0.48/0.70  thf('30', plain,
% 0.48/0.70      (![X8 : $i, X9 : $i]:
% 0.48/0.70         ((k4_xboole_0 @ X8 @ X9)
% 0.48/0.70           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.70  thf('31', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.48/0.70           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['29', '30'])).
% 0.48/0.70  thf('32', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.48/0.70      inference('cnf', [status(esa)], [t5_boole])).
% 0.48/0.70  thf('33', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.48/0.70      inference('demod', [status(thm)], ['31', '32'])).
% 0.48/0.70  thf('34', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.48/0.70      inference('sup+', [status(thm)], ['24', '33'])).
% 0.48/0.70  thf('35', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 0.48/0.70      inference('sup+', [status(thm)], ['5', '6'])).
% 0.48/0.70  thf('36', plain,
% 0.48/0.70      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C)),
% 0.48/0.70      inference('sup+', [status(thm)], ['34', '35'])).
% 0.48/0.70  thf('37', plain,
% 0.48/0.70      (![X2 : $i, X3 : $i]:
% 0.48/0.70         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.48/0.70      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.48/0.70  thf('38', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C) = (k1_xboole_0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['36', '37'])).
% 0.48/0.70  thf('39', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.70  thf('40', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((k3_xboole_0 @ sk_C @ (k3_xboole_0 @ X0 @ sk_A)) = (k1_xboole_0))),
% 0.48/0.70      inference('demod', [status(thm)], ['38', '39'])).
% 0.48/0.70  thf('41', plain,
% 0.48/0.70      (![X8 : $i, X9 : $i]:
% 0.48/0.70         ((k4_xboole_0 @ X8 @ X9)
% 0.48/0.70           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.70  thf('42', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((k4_xboole_0 @ sk_C @ (k3_xboole_0 @ X0 @ sk_A))
% 0.48/0.70           = (k5_xboole_0 @ sk_C @ k1_xboole_0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['40', '41'])).
% 0.48/0.70  thf('43', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.48/0.70      inference('cnf', [status(esa)], [t5_boole])).
% 0.48/0.70  thf('44', plain,
% 0.48/0.70      (![X0 : $i]: ((k4_xboole_0 @ sk_C @ (k3_xboole_0 @ X0 @ sk_A)) = (sk_C))),
% 0.48/0.70      inference('demod', [status(thm)], ['42', '43'])).
% 0.48/0.70  thf('45', plain,
% 0.48/0.70      (![X0 : $i]: ((k4_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ X0)) = (sk_C))),
% 0.48/0.70      inference('sup+', [status(thm)], ['15', '44'])).
% 0.48/0.70  thf('46', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.48/0.70      inference('demod', [status(thm)], ['31', '32'])).
% 0.48/0.70  thf('47', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_C)
% 0.48/0.70           = (k3_xboole_0 @ sk_A @ X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['45', '46'])).
% 0.48/0.70  thf('48', plain,
% 0.48/0.70      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.48/0.70         ((k3_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 0.48/0.70           = (k4_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14))),
% 0.48/0.70      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.48/0.70  thf('49', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))
% 0.48/0.70           = (k3_xboole_0 @ sk_A @ X0))),
% 0.48/0.70      inference('demod', [status(thm)], ['47', '48'])).
% 0.48/0.70  thf('50', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.70  thf('51', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.48/0.70      inference('demod', [status(thm)], ['14', '49', '50'])).
% 0.48/0.70  thf('52', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.48/0.70      inference('demod', [status(thm)], ['27', '28'])).
% 0.48/0.70  thf('53', plain,
% 0.48/0.70      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.48/0.70         ((k3_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 0.48/0.70           = (k4_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14))),
% 0.48/0.70      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.48/0.70  thf(l32_xboole_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.48/0.70  thf('54', plain,
% 0.48/0.70      (![X5 : $i, X6 : $i]:
% 0.48/0.70         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.48/0.70      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.48/0.70  thf('55', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.48/0.70          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.70  thf('56', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         (((k1_xboole_0) != (k1_xboole_0))
% 0.48/0.70          | (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['52', '55'])).
% 0.48/0.70  thf('57', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.48/0.70      inference('simplify', [status(thm)], ['56'])).
% 0.48/0.70  thf('58', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.48/0.70      inference('sup+', [status(thm)], ['51', '57'])).
% 0.48/0.70  thf('59', plain, ($false), inference('demod', [status(thm)], ['13', '58'])).
% 0.48/0.70  
% 0.48/0.70  % SZS output end Refutation
% 0.48/0.70  
% 0.48/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
