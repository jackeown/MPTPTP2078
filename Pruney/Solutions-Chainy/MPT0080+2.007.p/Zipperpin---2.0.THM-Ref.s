%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J4j1RcI5uc

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:05 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 163 expanded)
%              Number of leaves         :   19 (  58 expanded)
%              Depth                    :   17
%              Number of atoms          :  542 (1181 expanded)
%              Number of equality atoms :   59 ( 123 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    r1_tarski @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('43',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','45'])).

thf('47',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ sk_C )
      = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','55'])).

thf('57',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','56'])).

thf('58',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('59',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['0','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J4j1RcI5uc
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.93  % Solved by: fo/fo7.sh
% 0.75/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.93  % done 981 iterations in 0.475s
% 0.75/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.93  % SZS output start Refutation
% 0.75/0.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.93  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.75/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(t73_xboole_1, conjecture,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.75/0.93       ( r1_tarski @ A @ B ) ))).
% 0.75/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.93    (~( ![A:$i,B:$i,C:$i]:
% 0.75/0.93        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.75/0.93            ( r1_xboole_0 @ A @ C ) ) =>
% 0.75/0.93          ( r1_tarski @ A @ B ) ) )),
% 0.75/0.93    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.75/0.93  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('1', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(l32_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.75/0.93  thf('2', plain,
% 0.75/0.93      (![X7 : $i, X9 : $i]:
% 0.75/0.93         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.75/0.93      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/0.93  thf('3', plain,
% 0.75/0.93      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.93  thf(t48_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.75/0.93  thf('4', plain,
% 0.75/0.93      (![X16 : $i, X17 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.75/0.93           = (k3_xboole_0 @ X16 @ X17))),
% 0.75/0.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.93  thf(t41_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.75/0.93       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.75/0.93  thf('5', plain,
% 0.75/0.93      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.75/0.93           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.75/0.93  thf('6', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.75/0.93           = (k4_xboole_0 @ X2 @ 
% 0.75/0.93              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.75/0.93      inference('sup+', [status(thm)], ['4', '5'])).
% 0.75/0.93  thf('7', plain,
% 0.75/0.93      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.75/0.93           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.75/0.93  thf('8', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.75/0.93           = (k4_xboole_0 @ X2 @ 
% 0.75/0.93              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.75/0.93      inference('demod', [status(thm)], ['6', '7'])).
% 0.75/0.93  thf('9', plain,
% 0.75/0.93      (((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 0.75/0.93         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ k1_xboole_0)))),
% 0.75/0.93      inference('sup+', [status(thm)], ['3', '8'])).
% 0.75/0.93  thf(commutativity_k3_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.75/0.93  thf('10', plain,
% 0.75/0.93      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.93  thf(commutativity_k2_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.75/0.93  thf('11', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.93  thf('12', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.93  thf(t1_boole, axiom,
% 0.75/0.93    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.75/0.93  thf('13', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.75/0.93      inference('cnf', [status(esa)], [t1_boole])).
% 0.75/0.93  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.75/0.93      inference('sup+', [status(thm)], ['12', '13'])).
% 0.75/0.93  thf('15', plain,
% 0.75/0.93      (((k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.75/0.93         = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.75/0.93      inference('demod', [status(thm)], ['9', '10', '11', '14'])).
% 0.75/0.93  thf('16', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.93  thf(t7_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.75/0.93  thf('17', plain,
% 0.75/0.93      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 0.75/0.93      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.75/0.93  thf('18', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.75/0.93      inference('sup+', [status(thm)], ['16', '17'])).
% 0.75/0.93  thf('19', plain,
% 0.75/0.93      (![X7 : $i, X9 : $i]:
% 0.75/0.93         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.75/0.93      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/0.93  thf('20', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['18', '19'])).
% 0.75/0.93  thf('21', plain,
% 0.75/0.93      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.75/0.93           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.75/0.93  thf('22', plain,
% 0.75/0.93      (![X7 : $i, X8 : $i]:
% 0.75/0.93         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 0.75/0.93      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/0.93  thf('23', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.75/0.93          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['21', '22'])).
% 0.75/0.93  thf('24', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         (((k1_xboole_0) != (k1_xboole_0))
% 0.75/0.93          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['20', '23'])).
% 0.75/0.93  thf('25', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.75/0.93      inference('simplify', [status(thm)], ['24'])).
% 0.75/0.93  thf(t12_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.75/0.93  thf('26', plain,
% 0.75/0.93      (![X10 : $i, X11 : $i]:
% 0.75/0.93         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.75/0.93      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.75/0.93  thf('27', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['25', '26'])).
% 0.75/0.93  thf('28', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.93  thf('29', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.75/0.93      inference('demod', [status(thm)], ['27', '28'])).
% 0.75/0.93  thf('30', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(d7_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.75/0.93       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.75/0.93  thf('31', plain,
% 0.75/0.93      (![X4 : $i, X5 : $i]:
% 0.75/0.93         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.75/0.93      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.75/0.93  thf('32', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['30', '31'])).
% 0.75/0.93  thf('33', plain,
% 0.75/0.93      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.93  thf('34', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.75/0.93      inference('demod', [status(thm)], ['32', '33'])).
% 0.75/0.93  thf('35', plain,
% 0.75/0.93      (![X16 : $i, X17 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.75/0.93           = (k3_xboole_0 @ X16 @ X17))),
% 0.75/0.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.93  thf('36', plain,
% 0.75/0.93      (![X7 : $i, X8 : $i]:
% 0.75/0.93         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 0.75/0.93      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/0.93  thf('37', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.75/0.93          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['35', '36'])).
% 0.75/0.93  thf('38', plain,
% 0.75/0.93      ((((k1_xboole_0) != (k1_xboole_0))
% 0.75/0.93        | (r1_tarski @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['34', '37'])).
% 0.75/0.93  thf('39', plain, ((r1_tarski @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A))),
% 0.75/0.93      inference('simplify', [status(thm)], ['38'])).
% 0.75/0.93  thf('40', plain,
% 0.75/0.93      (![X10 : $i, X11 : $i]:
% 0.75/0.93         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.75/0.93      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.75/0.93  thf('41', plain,
% 0.75/0.93      (((k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A))
% 0.75/0.93         = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.75/0.93      inference('sup-', [status(thm)], ['39', '40'])).
% 0.75/0.93  thf('42', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.75/0.93      inference('demod', [status(thm)], ['27', '28'])).
% 0.75/0.93  thf('43', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.75/0.93      inference('demod', [status(thm)], ['41', '42'])).
% 0.75/0.93  thf('44', plain,
% 0.75/0.93      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.75/0.93           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.75/0.93  thf('45', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ sk_C @ X0)
% 0.75/0.93           = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.75/0.93      inference('sup+', [status(thm)], ['43', '44'])).
% 0.75/0.93  thf('46', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ X0))
% 0.75/0.93           = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.75/0.93      inference('sup+', [status(thm)], ['29', '45'])).
% 0.75/0.93  thf('47', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.75/0.93      inference('demod', [status(thm)], ['41', '42'])).
% 0.75/0.93  thf('48', plain,
% 0.75/0.93      (![X0 : $i]: ((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ X0)) = (sk_C))),
% 0.75/0.93      inference('demod', [status(thm)], ['46', '47'])).
% 0.75/0.93  thf('49', plain,
% 0.75/0.93      (![X16 : $i, X17 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.75/0.93           = (k3_xboole_0 @ X16 @ X17))),
% 0.75/0.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.93  thf('50', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((k4_xboole_0 @ sk_C @ sk_C)
% 0.75/0.93           = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.75/0.93      inference('sup+', [status(thm)], ['48', '49'])).
% 0.75/0.93  thf('51', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.75/0.93      inference('cnf', [status(esa)], [t1_boole])).
% 0.75/0.93  thf('52', plain,
% 0.75/0.93      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 0.75/0.93      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.75/0.93  thf('53', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.75/0.93      inference('sup+', [status(thm)], ['51', '52'])).
% 0.75/0.93  thf('54', plain,
% 0.75/0.93      (![X7 : $i, X9 : $i]:
% 0.75/0.93         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.75/0.93      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/0.93  thf('55', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['53', '54'])).
% 0.75/0.93  thf('56', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((k1_xboole_0) = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.75/0.93      inference('demod', [status(thm)], ['50', '55'])).
% 0.75/0.93  thf('57', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.75/0.93      inference('demod', [status(thm)], ['15', '56'])).
% 0.75/0.93  thf('58', plain,
% 0.75/0.93      (![X7 : $i, X8 : $i]:
% 0.75/0.93         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 0.75/0.93      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.75/0.93  thf('59', plain,
% 0.75/0.93      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['57', '58'])).
% 0.75/0.93  thf('60', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.75/0.93      inference('simplify', [status(thm)], ['59'])).
% 0.75/0.93  thf('61', plain, ($false), inference('demod', [status(thm)], ['0', '60'])).
% 0.75/0.93  
% 0.75/0.93  % SZS output end Refutation
% 0.75/0.93  
% 0.75/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
