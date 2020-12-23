%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fXKNSeZEw6

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:32 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 105 expanded)
%              Number of leaves         :   20 (  40 expanded)
%              Depth                    :   20
%              Number of atoms          :  529 ( 714 expanded)
%              Number of equality atoms :   58 (  76 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t63_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['6','23'])).

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('35',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','45','46'])).

thf('48',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','51'])).

thf('53',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference('sup+',[status(thm)],['3','52'])).

thf('54',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('59',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['0','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fXKNSeZEw6
% 0.11/0.34  % Computer   : n022.cluster.edu
% 0.11/0.34  % Model      : x86_64 x86_64
% 0.11/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.34  % Memory     : 8042.1875MB
% 0.11/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.34  % CPULimit   : 60
% 0.11/0.34  % DateTime   : Tue Dec  1 11:59:26 EST 2020
% 0.11/0.34  % CPUTime    : 
% 0.11/0.34  % Running portfolio for 600 s
% 0.11/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.34  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.77/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.77/0.96  % Solved by: fo/fo7.sh
% 0.77/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.96  % done 1000 iterations in 0.510s
% 0.77/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.77/0.96  % SZS output start Refutation
% 0.77/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.77/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.96  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.77/0.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.77/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.96  thf(sk_C_type, type, sk_C: $i).
% 0.77/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.96  thf(t63_xboole_1, conjecture,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.77/0.96       ( r1_xboole_0 @ A @ C ) ))).
% 0.77/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.96    (~( ![A:$i,B:$i,C:$i]:
% 0.77/0.96        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.77/0.96          ( r1_xboole_0 @ A @ C ) ) )),
% 0.77/0.96    inference('cnf.neg', [status(esa)], [t63_xboole_1])).
% 0.77/0.96  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(t28_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.77/0.96  thf('2', plain,
% 0.77/0.96      (![X9 : $i, X10 : $i]:
% 0.77/0.96         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.77/0.96      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.77/0.96  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/0.96  thf(commutativity_k3_xboole_0, axiom,
% 0.77/0.96    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.77/0.96  thf('4', plain,
% 0.77/0.96      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.96  thf(t48_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.77/0.96  thf('5', plain,
% 0.77/0.96      (![X17 : $i, X18 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.77/0.96           = (k3_xboole_0 @ X17 @ X18))),
% 0.77/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.96  thf(commutativity_k2_xboole_0, axiom,
% 0.77/0.96    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.77/0.96  thf('6', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.96  thf('7', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(d7_xboole_0, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.77/0.96       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.77/0.96  thf('8', plain,
% 0.77/0.96      (![X4 : $i, X5 : $i]:
% 0.77/0.96         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.77/0.96      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.77/0.96  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['7', '8'])).
% 0.77/0.96  thf('10', plain,
% 0.77/0.96      (![X17 : $i, X18 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.77/0.96           = (k3_xboole_0 @ X17 @ X18))),
% 0.77/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.96  thf('11', plain,
% 0.77/0.96      (![X17 : $i, X18 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.77/0.96           = (k3_xboole_0 @ X17 @ X18))),
% 0.77/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.96  thf('12', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.77/0.96           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['10', '11'])).
% 0.77/0.96  thf(t36_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.77/0.96  thf('13', plain,
% 0.77/0.96      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.77/0.96      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.77/0.96  thf('14', plain,
% 0.77/0.96      (![X9 : $i, X10 : $i]:
% 0.77/0.96         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.77/0.96      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.77/0.96  thf('15', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.77/0.96           = (k4_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('sup-', [status(thm)], ['13', '14'])).
% 0.77/0.96  thf('16', plain,
% 0.77/0.96      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.96  thf('17', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.77/0.96           = (k4_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('demod', [status(thm)], ['15', '16'])).
% 0.77/0.96  thf('18', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.77/0.96           = (k4_xboole_0 @ X1 @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['12', '17'])).
% 0.77/0.96  thf('19', plain,
% 0.77/0.96      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.77/0.96      inference('sup+', [status(thm)], ['9', '18'])).
% 0.77/0.96  thf(t3_boole, axiom,
% 0.77/0.96    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.77/0.96  thf('20', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.77/0.96      inference('cnf', [status(esa)], [t3_boole])).
% 0.77/0.96  thf('21', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.77/0.96      inference('demod', [status(thm)], ['19', '20'])).
% 0.77/0.96  thf(t41_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.77/0.96       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.77/0.96  thf('22', plain,
% 0.77/0.96      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.77/0.96           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.77/0.96      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.77/0.96  thf('23', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ sk_B @ X0)
% 0.77/0.96           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['21', '22'])).
% 0.77/0.96  thf('24', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ sk_B @ X0)
% 0.77/0.96           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_C)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['6', '23'])).
% 0.77/0.96  thf('25', plain,
% 0.77/0.96      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.77/0.96           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.77/0.96      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.77/0.96  thf('26', plain,
% 0.77/0.96      (![X17 : $i, X18 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.77/0.96           = (k3_xboole_0 @ X17 @ X18))),
% 0.77/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.96  thf('27', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X2 @ 
% 0.77/0.96           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 0.77/0.96           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['25', '26'])).
% 0.77/0.96  thf('28', plain,
% 0.77/0.96      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.77/0.96           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.77/0.96      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.77/0.96  thf('29', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X2 @ 
% 0.77/0.96           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 0.77/0.96           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['27', '28'])).
% 0.77/0.96  thf('30', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ X0)))
% 0.77/0.96           = (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_C))),
% 0.77/0.96      inference('sup+', [status(thm)], ['24', '29'])).
% 0.77/0.96  thf('31', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.77/0.96      inference('cnf', [status(esa)], [t3_boole])).
% 0.77/0.96  thf('32', plain,
% 0.77/0.96      (![X17 : $i, X18 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.77/0.96           = (k3_xboole_0 @ X17 @ X18))),
% 0.77/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.96  thf('33', plain,
% 0.77/0.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['31', '32'])).
% 0.77/0.96  thf('34', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.96  thf(t1_boole, axiom,
% 0.77/0.96    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.77/0.96  thf('35', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.77/0.96      inference('cnf', [status(esa)], [t1_boole])).
% 0.77/0.96  thf('36', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['34', '35'])).
% 0.77/0.96  thf(t7_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.77/0.96  thf('37', plain,
% 0.77/0.96      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 0.77/0.96      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.77/0.96  thf('38', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.77/0.96      inference('sup+', [status(thm)], ['36', '37'])).
% 0.77/0.96  thf('39', plain,
% 0.77/0.96      (![X9 : $i, X10 : $i]:
% 0.77/0.96         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.77/0.96      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.77/0.96  thf('40', plain,
% 0.77/0.96      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['38', '39'])).
% 0.77/0.96  thf('41', plain,
% 0.77/0.96      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.96  thf('42', plain,
% 0.77/0.96      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['40', '41'])).
% 0.77/0.96  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.77/0.96      inference('demod', [status(thm)], ['33', '42'])).
% 0.77/0.96  thf('44', plain,
% 0.77/0.96      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.77/0.96           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.77/0.96      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.77/0.96  thf('45', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k1_xboole_0)
% 0.77/0.96           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.77/0.96      inference('sup+', [status(thm)], ['43', '44'])).
% 0.77/0.96  thf('46', plain,
% 0.77/0.96      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.96  thf('47', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((k1_xboole_0) = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.77/0.96      inference('demod', [status(thm)], ['30', '45', '46'])).
% 0.77/0.96  thf('48', plain,
% 0.77/0.96      (![X4 : $i, X6 : $i]:
% 0.77/0.96         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.77/0.96      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.77/0.96  thf('49', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (((k1_xboole_0) != (k1_xboole_0))
% 0.77/0.96          | (r1_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['47', '48'])).
% 0.77/0.96  thf('50', plain,
% 0.77/0.96      (![X0 : $i]: (r1_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ X0))),
% 0.77/0.96      inference('simplify', [status(thm)], ['49'])).
% 0.77/0.96  thf('51', plain,
% 0.77/0.96      (![X0 : $i]: (r1_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_B @ X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['5', '50'])).
% 0.77/0.96  thf('52', plain,
% 0.77/0.96      (![X0 : $i]: (r1_xboole_0 @ sk_C @ (k3_xboole_0 @ X0 @ sk_B))),
% 0.77/0.96      inference('sup+', [status(thm)], ['4', '51'])).
% 0.77/0.96  thf('53', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.77/0.96      inference('sup+', [status(thm)], ['3', '52'])).
% 0.77/0.96  thf('54', plain,
% 0.77/0.96      (![X4 : $i, X5 : $i]:
% 0.77/0.96         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.77/0.96      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.77/0.96  thf('55', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['53', '54'])).
% 0.77/0.96  thf('56', plain,
% 0.77/0.96      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.96  thf('57', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.77/0.96      inference('demod', [status(thm)], ['55', '56'])).
% 0.77/0.96  thf('58', plain,
% 0.77/0.96      (![X4 : $i, X6 : $i]:
% 0.77/0.96         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.77/0.96      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.77/0.96  thf('59', plain,
% 0.77/0.96      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C))),
% 0.77/0.96      inference('sup-', [status(thm)], ['57', '58'])).
% 0.77/0.96  thf('60', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.77/0.96      inference('simplify', [status(thm)], ['59'])).
% 0.77/0.96  thf('61', plain, ($false), inference('demod', [status(thm)], ['0', '60'])).
% 0.77/0.96  
% 0.77/0.96  % SZS output end Refutation
% 0.77/0.96  
% 0.77/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
