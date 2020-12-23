%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CKtBaYygF0

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:22 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   77 (  98 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  495 ( 640 expanded)
%              Number of equality atoms :   61 (  82 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t14_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t14_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X42: $i,X43: $i] :
      ( r1_tarski @ ( k1_tarski @ X42 ) @ ( k2_tarski @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

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

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k4_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) @ k1_xboole_0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k4_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k4_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('25',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k4_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('35',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['22','47'])).

thf('49',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','50'])).

thf('52',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','51'])).

thf('53',plain,(
    $false ),
    inference(simplify,[status(thm)],['52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CKtBaYygF0
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.62  % Solved by: fo/fo7.sh
% 0.36/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.62  % done 413 iterations in 0.177s
% 0.36/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.62  % SZS output start Refutation
% 0.36/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.62  thf(t14_zfmisc_1, conjecture,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.36/0.62       ( k2_tarski @ A @ B ) ))).
% 0.36/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.62    (~( ![A:$i,B:$i]:
% 0.36/0.62        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.36/0.62          ( k2_tarski @ A @ B ) ) )),
% 0.36/0.62    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 0.36/0.62  thf('0', plain,
% 0.36/0.62      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.36/0.62         != (k2_tarski @ sk_A @ sk_B))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf(t12_zfmisc_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.36/0.62  thf('1', plain,
% 0.36/0.62      (![X42 : $i, X43 : $i]:
% 0.36/0.62         (r1_tarski @ (k1_tarski @ X42) @ (k2_tarski @ X42 @ X43))),
% 0.36/0.62      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.36/0.62  thf(l32_xboole_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.62  thf('2', plain,
% 0.36/0.62      (![X5 : $i, X7 : $i]:
% 0.36/0.62         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.36/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.62  thf('3', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.36/0.62           = (k1_xboole_0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.62  thf(t51_xboole_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.36/0.62       ( A ) ))).
% 0.36/0.62  thf('4', plain,
% 0.36/0.62      (![X14 : $i, X15 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ (k4_xboole_0 @ X14 @ X15))
% 0.36/0.62           = (X14))),
% 0.36/0.62      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.36/0.62  thf('5', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ 
% 0.36/0.62           (k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1)) @ 
% 0.36/0.62           k1_xboole_0) = (k1_tarski @ X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['3', '4'])).
% 0.36/0.62  thf(t1_boole, axiom,
% 0.36/0.62    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.62  thf('6', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.36/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.36/0.62  thf('7', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.36/0.62           = (k1_tarski @ X0))),
% 0.36/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.36/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.36/0.62  thf('8', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.62  thf('9', plain,
% 0.36/0.62      (![X14 : $i, X15 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ (k4_xboole_0 @ X14 @ X15))
% 0.36/0.62           = (X14))),
% 0.36/0.62      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.36/0.62  thf(t46_xboole_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.36/0.62  thf('10', plain,
% 0.36/0.62      (![X12 : $i, X13 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (k1_xboole_0))),
% 0.36/0.62      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.36/0.62  thf('11', plain,
% 0.36/0.62      (![X5 : $i, X6 : $i]:
% 0.36/0.62         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.36/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.62  thf('12', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         (((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.62          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.62  thf('13', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.36/0.62      inference('simplify', [status(thm)], ['12'])).
% 0.36/0.62  thf('14', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.36/0.62      inference('sup+', [status(thm)], ['9', '13'])).
% 0.36/0.62  thf('15', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.36/0.62      inference('sup+', [status(thm)], ['8', '14'])).
% 0.36/0.62  thf('16', plain,
% 0.36/0.62      (![X5 : $i, X7 : $i]:
% 0.36/0.62         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.36/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.62  thf('17', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.62  thf('18', plain,
% 0.36/0.62      (![X14 : $i, X15 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ (k4_xboole_0 @ X14 @ X15))
% 0.36/0.62           = (X14))),
% 0.36/0.62      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.36/0.62  thf('19', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) @ 
% 0.36/0.62           k1_xboole_0) = (k3_xboole_0 @ X1 @ X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['17', '18'])).
% 0.36/0.62  thf('20', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.62  thf('21', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.36/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.36/0.62  thf('22', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.36/0.62           = (k3_xboole_0 @ X1 @ X0))),
% 0.36/0.62      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.36/0.62  thf(t100_xboole_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.62  thf('23', plain,
% 0.36/0.62      (![X8 : $i, X9 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ X8 @ X9)
% 0.36/0.62           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.62  thf(commutativity_k5_xboole_0, axiom,
% 0.36/0.62    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.36/0.62  thf('24', plain,
% 0.36/0.62      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.36/0.62      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.36/0.62  thf(idempotence_k2_xboole_0, axiom,
% 0.36/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.36/0.62  thf('25', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.36/0.62      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.36/0.62  thf('26', plain,
% 0.36/0.62      (![X12 : $i, X13 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (k1_xboole_0))),
% 0.36/0.62      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.36/0.62  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['25', '26'])).
% 0.36/0.62  thf('28', plain,
% 0.36/0.62      (![X14 : $i, X15 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ (k4_xboole_0 @ X14 @ X15))
% 0.36/0.62           = (X14))),
% 0.36/0.62      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.36/0.62  thf('29', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ k1_xboole_0) = (X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['27', '28'])).
% 0.36/0.62  thf('30', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.36/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.36/0.62  thf('31', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.62      inference('demod', [status(thm)], ['29', '30'])).
% 0.36/0.62  thf('32', plain,
% 0.36/0.62      (![X8 : $i, X9 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ X8 @ X9)
% 0.36/0.62           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.62  thf('33', plain,
% 0.36/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.36/0.62  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['25', '26'])).
% 0.36/0.62  thf('35', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.36/0.62      inference('demod', [status(thm)], ['33', '34'])).
% 0.36/0.62  thf(t91_xboole_1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.36/0.62       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.36/0.62  thf('36', plain,
% 0.36/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.36/0.62           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.36/0.62  thf('37', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.36/0.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.36/0.62      inference('sup+', [status(thm)], ['35', '36'])).
% 0.36/0.62  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['25', '26'])).
% 0.36/0.62  thf(t98_xboole_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.36/0.62  thf('39', plain,
% 0.36/0.62      (![X19 : $i, X20 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ X19 @ X20)
% 0.36/0.62           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.62  thf('40', plain,
% 0.36/0.62      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['38', '39'])).
% 0.36/0.62  thf('41', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.36/0.62      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.36/0.62  thf('42', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.62      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.62  thf('43', plain,
% 0.36/0.62      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.36/0.62      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.36/0.62  thf('44', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['42', '43'])).
% 0.36/0.62  thf('45', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.36/0.62      inference('demod', [status(thm)], ['37', '44'])).
% 0.36/0.62  thf('46', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.36/0.62      inference('sup+', [status(thm)], ['24', '45'])).
% 0.36/0.62  thf('47', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((X1)
% 0.36/0.62           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.36/0.62      inference('sup+', [status(thm)], ['23', '46'])).
% 0.36/0.62  thf('48', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((X0)
% 0.36/0.62           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.36/0.62              (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.36/0.62      inference('sup+', [status(thm)], ['22', '47'])).
% 0.36/0.62  thf('49', plain,
% 0.36/0.62      (![X19 : $i, X20 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ X19 @ X20)
% 0.36/0.62           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.62  thf('50', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((X0) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.36/0.62      inference('demod', [status(thm)], ['48', '49'])).
% 0.36/0.62  thf('51', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k2_tarski @ X0 @ X1)
% 0.36/0.62           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1)))),
% 0.36/0.62      inference('sup+', [status(thm)], ['7', '50'])).
% 0.36/0.62  thf('52', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['0', '51'])).
% 0.36/0.62  thf('53', plain, ($false), inference('simplify', [status(thm)], ['52'])).
% 0.36/0.62  
% 0.36/0.62  % SZS output end Refutation
% 0.36/0.62  
% 0.36/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
