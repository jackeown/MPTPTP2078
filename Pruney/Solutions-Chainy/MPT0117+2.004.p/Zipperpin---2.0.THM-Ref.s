%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zwOgBGBWJr

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 115 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :  485 ( 807 expanded)
%              Number of equality atoms :   54 (  82 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t110_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ B ) )
       => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t110_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t99_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) @ ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X16 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[t99_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ sk_A ) @ sk_B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_C @ sk_A ) @ sk_B )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['3','13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('17',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('19',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('20',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_C @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','20','21','30'])).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k5_xboole_0 @ sk_C @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_C @ sk_A ) @ sk_B ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) @ ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X16 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[t99_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) @ ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X16 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[t99_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X2 ) @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['34','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zwOgBGBWJr
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:15:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 95 iterations in 0.058s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(t110_xboole_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.21/0.51       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.51        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.21/0.51          ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t110_xboole_1])).
% 0.21/0.51  thf('0', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(l32_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X4 : $i, X6 : $i]:
% 0.21/0.51         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.51  thf('3', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('4', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X4 : $i, X6 : $i]:
% 0.21/0.51         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.51  thf('6', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf(t98_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ X14 @ X15)
% 0.21/0.51           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (((k2_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.51  thf(t5_boole, axiom,
% 0.21/0.51    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.51  thf('10', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.51  thf('11', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.51  thf(t99_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.51       ( k2_xboole_0 @
% 0.21/0.51         ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ 
% 0.21/0.51         ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ))).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         ((k4_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.21/0.51           = (k2_xboole_0 @ (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)) @ 
% 0.21/0.51              (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X16 @ X18))))),
% 0.21/0.51      inference('cnf', [status(esa)], [t99_xboole_1])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ sk_A) @ sk_B)
% 0.21/0.51           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ 
% 0.21/0.51              (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (((k4_xboole_0 @ (k5_xboole_0 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.51         = (k2_xboole_0 @ k1_xboole_0 @ 
% 0.21/0.51            (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['3', '13'])).
% 0.21/0.51  thf('15', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ X14 @ X15)
% 0.21/0.51           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (((k2_xboole_0 @ sk_B @ sk_C) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.51  thf('19', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.51  thf('20', plain, (((k2_xboole_0 @ sk_C @ sk_B) = (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.51  thf('21', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.51  thf('22', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X4 : $i, X6 : $i]:
% 0.21/0.51         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ X14 @ X15)
% 0.21/0.51           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('27', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.51  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.51  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (((k4_xboole_0 @ (k5_xboole_0 @ sk_C @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '20', '21', '30'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.51        | (r1_tarski @ (k5_xboole_0 @ sk_C @ sk_A) @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.51  thf('34', plain, ((r1_tarski @ (k5_xboole_0 @ sk_C @ sk_A) @ sk_B)),
% 0.21/0.51      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.51  thf('35', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.51  thf(t28_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.51  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf(t100_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i]:
% 0.21/0.51         ((k4_xboole_0 @ X7 @ X8)
% 0.21/0.51           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('42', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.51  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         ((k4_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.21/0.51           = (k2_xboole_0 @ (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)) @ 
% 0.21/0.51              (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X16 @ X18))))),
% 0.21/0.51      inference('cnf', [status(esa)], [t99_xboole_1])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ X0)) @ 
% 0.21/0.51           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.21/0.51           = (k4_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         ((k4_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.21/0.51           = (k2_xboole_0 @ (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)) @ 
% 0.21/0.51              (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X16 @ X18))))),
% 0.21/0.51      inference('cnf', [status(esa)], [t99_xboole_1])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X2) @ X0)
% 0.21/0.51           = (k4_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['46', '47'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k5_xboole_0 @ X1 @ X0)
% 0.21/0.51           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['43', '48'])).
% 0.21/0.51  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('52', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['34', '51'])).
% 0.21/0.51  thf('53', plain, ($false), inference('demod', [status(thm)], ['0', '52'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
