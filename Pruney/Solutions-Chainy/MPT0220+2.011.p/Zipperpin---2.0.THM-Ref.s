%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bQ5YzHDjHs

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:19 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 252 expanded)
%              Number of leaves         :   21 (  87 expanded)
%              Depth                    :   19
%              Number of atoms          :  586 (1833 expanded)
%              Number of equality atoms :   69 ( 222 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ! [X48: $i,X49: $i] :
      ( r1_tarski @ ( k1_tarski @ X48 ) @ ( k2_tarski @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','34'])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('51',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('52',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('55',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','56'])).

thf('58',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','59'])).

thf('61',plain,(
    $false ),
    inference(simplify,[status(thm)],['60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bQ5YzHDjHs
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:32:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.06/1.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.23  % Solved by: fo/fo7.sh
% 1.06/1.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.23  % done 698 iterations in 0.777s
% 1.06/1.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.23  % SZS output start Refutation
% 1.06/1.23  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.06/1.23  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.23  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.06/1.23  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.06/1.23  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.06/1.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.23  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.06/1.23  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.23  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.06/1.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.23  thf(t14_zfmisc_1, conjecture,
% 1.06/1.23    (![A:$i,B:$i]:
% 1.06/1.23     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 1.06/1.23       ( k2_tarski @ A @ B ) ))).
% 1.06/1.23  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.23    (~( ![A:$i,B:$i]:
% 1.06/1.23        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 1.06/1.23          ( k2_tarski @ A @ B ) ) )),
% 1.06/1.23    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 1.06/1.23  thf('0', plain,
% 1.06/1.23      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 1.06/1.23         != (k2_tarski @ sk_A @ sk_B))),
% 1.06/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.23  thf(t12_zfmisc_1, axiom,
% 1.06/1.23    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 1.06/1.23  thf('1', plain,
% 1.06/1.23      (![X48 : $i, X49 : $i]:
% 1.06/1.23         (r1_tarski @ (k1_tarski @ X48) @ (k2_tarski @ X48 @ X49))),
% 1.06/1.23      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 1.06/1.23  thf(t28_xboole_1, axiom,
% 1.06/1.23    (![A:$i,B:$i]:
% 1.06/1.23     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.06/1.23  thf('2', plain,
% 1.06/1.23      (![X13 : $i, X14 : $i]:
% 1.06/1.23         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.06/1.23      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.06/1.23  thf('3', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 1.06/1.23           = (k1_tarski @ X1))),
% 1.06/1.23      inference('sup-', [status(thm)], ['1', '2'])).
% 1.06/1.23  thf(commutativity_k3_xboole_0, axiom,
% 1.06/1.23    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.06/1.23  thf('4', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.06/1.23  thf(t100_xboole_1, axiom,
% 1.06/1.23    (![A:$i,B:$i]:
% 1.06/1.23     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.06/1.23  thf('5', plain,
% 1.06/1.23      (![X10 : $i, X11 : $i]:
% 1.06/1.23         ((k4_xboole_0 @ X10 @ X11)
% 1.06/1.23           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.06/1.23      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.06/1.23  thf('6', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         ((k4_xboole_0 @ X0 @ X1)
% 1.06/1.23           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.06/1.23      inference('sup+', [status(thm)], ['4', '5'])).
% 1.06/1.23  thf('7', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         ((k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0))
% 1.06/1.23           = (k5_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0)))),
% 1.06/1.23      inference('sup+', [status(thm)], ['3', '6'])).
% 1.06/1.23  thf(commutativity_k5_xboole_0, axiom,
% 1.06/1.23    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.06/1.23  thf('8', plain,
% 1.06/1.23      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.06/1.23      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.06/1.23  thf('9', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         ((k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0))
% 1.06/1.23           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1)))),
% 1.06/1.23      inference('demod', [status(thm)], ['7', '8'])).
% 1.06/1.23  thf(d10_xboole_0, axiom,
% 1.06/1.23    (![A:$i,B:$i]:
% 1.06/1.23     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.06/1.23  thf('10', plain,
% 1.06/1.23      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.06/1.23      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.06/1.23  thf('11', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.06/1.23      inference('simplify', [status(thm)], ['10'])).
% 1.06/1.23  thf('12', plain,
% 1.06/1.23      (![X13 : $i, X14 : $i]:
% 1.06/1.23         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.06/1.23      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.06/1.23  thf('13', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.06/1.23      inference('sup-', [status(thm)], ['11', '12'])).
% 1.06/1.23  thf('14', plain,
% 1.06/1.23      (![X10 : $i, X11 : $i]:
% 1.06/1.23         ((k4_xboole_0 @ X10 @ X11)
% 1.06/1.23           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.06/1.23      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.06/1.23  thf('15', plain,
% 1.06/1.23      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.06/1.23      inference('sup+', [status(thm)], ['13', '14'])).
% 1.06/1.23  thf('16', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.06/1.23      inference('simplify', [status(thm)], ['10'])).
% 1.06/1.23  thf(l32_xboole_1, axiom,
% 1.06/1.23    (![A:$i,B:$i]:
% 1.06/1.23     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.06/1.23  thf('17', plain,
% 1.06/1.23      (![X7 : $i, X9 : $i]:
% 1.06/1.23         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 1.06/1.23      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.06/1.23  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.06/1.23      inference('sup-', [status(thm)], ['16', '17'])).
% 1.06/1.23  thf('19', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.06/1.23      inference('demod', [status(thm)], ['15', '18'])).
% 1.06/1.23  thf(t91_xboole_1, axiom,
% 1.06/1.23    (![A:$i,B:$i,C:$i]:
% 1.06/1.23     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.06/1.23       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.06/1.23  thf('20', plain,
% 1.06/1.23      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.06/1.23         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.06/1.23           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.06/1.23      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.06/1.23  thf('21', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.06/1.23           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.06/1.23      inference('sup+', [status(thm)], ['19', '20'])).
% 1.06/1.23  thf(t98_xboole_1, axiom,
% 1.06/1.23    (![A:$i,B:$i]:
% 1.06/1.23     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.06/1.23  thf('22', plain,
% 1.06/1.23      (![X18 : $i, X19 : $i]:
% 1.06/1.23         ((k2_xboole_0 @ X18 @ X19)
% 1.06/1.23           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 1.06/1.23      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.06/1.23  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.06/1.23      inference('sup-', [status(thm)], ['16', '17'])).
% 1.06/1.23  thf('24', plain,
% 1.06/1.23      (![X18 : $i, X19 : $i]:
% 1.06/1.23         ((k2_xboole_0 @ X18 @ X19)
% 1.06/1.23           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 1.06/1.23      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.06/1.23  thf('25', plain,
% 1.06/1.23      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.06/1.23      inference('sup+', [status(thm)], ['23', '24'])).
% 1.06/1.23  thf('26', plain,
% 1.06/1.23      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.06/1.23      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.06/1.23  thf('27', plain,
% 1.06/1.23      (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 1.06/1.23      inference('sup+', [status(thm)], ['25', '26'])).
% 1.06/1.23  thf('28', plain,
% 1.06/1.23      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.06/1.23      inference('sup+', [status(thm)], ['23', '24'])).
% 1.06/1.23  thf('29', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.06/1.23           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.06/1.23      inference('sup+', [status(thm)], ['19', '20'])).
% 1.06/1.23  thf('30', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         ((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 1.06/1.23           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)))),
% 1.06/1.23      inference('sup+', [status(thm)], ['28', '29'])).
% 1.06/1.23  thf('31', plain,
% 1.06/1.23      (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 1.06/1.23      inference('sup+', [status(thm)], ['25', '26'])).
% 1.06/1.23  thf(t1_boole, axiom,
% 1.06/1.23    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.06/1.23  thf('32', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.06/1.23      inference('cnf', [status(esa)], [t1_boole])).
% 1.06/1.23  thf('33', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)))),
% 1.06/1.23      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.06/1.23  thf('34', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.06/1.23      inference('sup+', [status(thm)], ['27', '33'])).
% 1.06/1.23  thf('35', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         ((k1_xboole_0)
% 1.06/1.23           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ 
% 1.06/1.23              (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.06/1.23      inference('sup+', [status(thm)], ['22', '34'])).
% 1.06/1.23  thf('36', plain,
% 1.06/1.23      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.06/1.23      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.06/1.23  thf('37', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         ((k1_xboole_0)
% 1.06/1.23           = (k5_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ 
% 1.06/1.23              (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.06/1.23      inference('demod', [status(thm)], ['35', '36'])).
% 1.06/1.23  thf('38', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.06/1.23           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.06/1.23      inference('sup+', [status(thm)], ['19', '20'])).
% 1.06/1.23  thf('39', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         ((k5_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 1.06/1.23           = (k5_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 1.06/1.23      inference('sup+', [status(thm)], ['37', '38'])).
% 1.06/1.23  thf('40', plain,
% 1.06/1.23      (![X18 : $i, X19 : $i]:
% 1.06/1.23         ((k2_xboole_0 @ X18 @ X19)
% 1.06/1.23           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 1.06/1.23      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.06/1.23  thf('41', plain,
% 1.06/1.23      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.06/1.23      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.06/1.23  thf('42', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 1.06/1.23           = (k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.06/1.23      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.06/1.23  thf('43', plain,
% 1.06/1.23      (![X10 : $i, X11 : $i]:
% 1.06/1.23         ((k4_xboole_0 @ X10 @ X11)
% 1.06/1.23           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.06/1.23      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.06/1.23  thf('44', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.06/1.23           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.06/1.23      inference('sup+', [status(thm)], ['19', '20'])).
% 1.06/1.23  thf('45', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         ((k5_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 1.06/1.23           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.06/1.23      inference('sup+', [status(thm)], ['43', '44'])).
% 1.06/1.23  thf('46', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         ((k4_xboole_0 @ X0 @ X1)
% 1.06/1.23           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.06/1.23      inference('sup+', [status(thm)], ['4', '5'])).
% 1.06/1.23  thf('47', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 1.06/1.23           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.06/1.23      inference('sup+', [status(thm)], ['45', '46'])).
% 1.06/1.23  thf('48', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.06/1.23           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.06/1.23      inference('sup+', [status(thm)], ['19', '20'])).
% 1.06/1.23  thf('49', plain,
% 1.06/1.23      (![X0 : $i]:
% 1.06/1.23         ((k5_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 1.06/1.23           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.06/1.23      inference('sup+', [status(thm)], ['47', '48'])).
% 1.06/1.23  thf('50', plain,
% 1.06/1.23      (![X18 : $i, X19 : $i]:
% 1.06/1.23         ((k2_xboole_0 @ X18 @ X19)
% 1.06/1.23           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 1.06/1.23      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.06/1.23  thf('51', plain,
% 1.06/1.23      (![X18 : $i, X19 : $i]:
% 1.06/1.23         ((k2_xboole_0 @ X18 @ X19)
% 1.06/1.23           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 1.06/1.23      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.06/1.23  thf('52', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.06/1.23      inference('cnf', [status(esa)], [t1_boole])).
% 1.06/1.23  thf('53', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.06/1.23      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 1.06/1.23  thf('54', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.06/1.23      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 1.06/1.23  thf('55', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 1.06/1.23      inference('demod', [status(thm)], ['42', '53', '54'])).
% 1.06/1.23  thf('56', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.06/1.23      inference('demod', [status(thm)], ['21', '55'])).
% 1.06/1.23  thf('57', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         ((k2_tarski @ X0 @ X1)
% 1.06/1.23           = (k5_xboole_0 @ (k1_tarski @ X0) @ 
% 1.06/1.23              (k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0))))),
% 1.06/1.23      inference('sup+', [status(thm)], ['9', '56'])).
% 1.06/1.23  thf('58', plain,
% 1.06/1.23      (![X18 : $i, X19 : $i]:
% 1.06/1.23         ((k2_xboole_0 @ X18 @ X19)
% 1.06/1.23           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 1.06/1.23      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.06/1.23  thf('59', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         ((k2_tarski @ X0 @ X1)
% 1.06/1.23           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1)))),
% 1.06/1.23      inference('demod', [status(thm)], ['57', '58'])).
% 1.06/1.23  thf('60', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 1.06/1.23      inference('demod', [status(thm)], ['0', '59'])).
% 1.06/1.23  thf('61', plain, ($false), inference('simplify', [status(thm)], ['60'])).
% 1.06/1.23  
% 1.06/1.23  % SZS output end Refutation
% 1.06/1.23  
% 1.06/1.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
