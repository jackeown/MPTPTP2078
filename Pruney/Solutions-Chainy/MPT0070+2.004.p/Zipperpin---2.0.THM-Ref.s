%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LKlq8p0JWD

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:32 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 261 expanded)
%              Number of leaves         :   19 (  93 expanded)
%              Depth                    :   19
%              Number of atoms          :  685 (1779 expanded)
%              Number of equality atoms :   81 ( 210 expanded)
%              Maximal formula depth    :   10 (   6 average)

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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','17'])).

thf('19',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_A ) )
      = ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','17'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('37',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['1','37'])).

thf('39',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('58',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('59',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('65',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('67',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_B )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('70',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_C ) )
      = ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['56','72'])).

thf('74',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_C ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','17'])).

thf('79',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['47','79'])).

thf('81',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('82',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['0','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LKlq8p0JWD
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:33:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.89/1.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.09  % Solved by: fo/fo7.sh
% 0.89/1.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.09  % done 1095 iterations in 0.638s
% 0.89/1.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.09  % SZS output start Refutation
% 0.89/1.09  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.89/1.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.09  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.89/1.09  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.89/1.09  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.09  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.89/1.09  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.09  thf(sk_C_type, type, sk_C: $i).
% 0.89/1.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.09  thf(t63_xboole_1, conjecture,
% 0.89/1.09    (![A:$i,B:$i,C:$i]:
% 0.89/1.09     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.89/1.09       ( r1_xboole_0 @ A @ C ) ))).
% 0.89/1.09  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.09    (~( ![A:$i,B:$i,C:$i]:
% 0.89/1.09        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.89/1.09          ( r1_xboole_0 @ A @ C ) ) )),
% 0.89/1.09    inference('cnf.neg', [status(esa)], [t63_xboole_1])).
% 0.89/1.09  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf(commutativity_k2_xboole_0, axiom,
% 0.89/1.09    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.89/1.09  thf('1', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.09  thf(t3_boole, axiom,
% 0.89/1.09    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.89/1.09  thf('2', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.89/1.09      inference('cnf', [status(esa)], [t3_boole])).
% 0.89/1.09  thf(t48_xboole_1, axiom,
% 0.89/1.09    (![A:$i,B:$i]:
% 0.89/1.09     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.89/1.09  thf('3', plain,
% 0.89/1.09      (![X19 : $i, X20 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.89/1.09           = (k3_xboole_0 @ X19 @ X20))),
% 0.89/1.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.09  thf('4', plain,
% 0.89/1.09      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.89/1.09      inference('sup+', [status(thm)], ['2', '3'])).
% 0.89/1.09  thf(t36_xboole_1, axiom,
% 0.89/1.09    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.89/1.09  thf('5', plain,
% 0.89/1.09      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.89/1.09      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.89/1.09  thf(t12_xboole_1, axiom,
% 0.89/1.09    (![A:$i,B:$i]:
% 0.89/1.09     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.89/1.09  thf('6', plain,
% 0.89/1.09      (![X10 : $i, X11 : $i]:
% 0.89/1.09         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.89/1.09      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.89/1.09  thf('7', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.89/1.09      inference('sup-', [status(thm)], ['5', '6'])).
% 0.89/1.09  thf('8', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.09  thf('9', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.89/1.09      inference('demod', [status(thm)], ['7', '8'])).
% 0.89/1.09  thf('10', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.09  thf(t1_boole, axiom,
% 0.89/1.09    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.89/1.09  thf('11', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.89/1.09      inference('cnf', [status(esa)], [t1_boole])).
% 0.89/1.09  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.89/1.09      inference('sup+', [status(thm)], ['10', '11'])).
% 0.89/1.09  thf('13', plain,
% 0.89/1.09      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.89/1.09      inference('sup+', [status(thm)], ['9', '12'])).
% 0.89/1.09  thf('14', plain,
% 0.89/1.09      (![X19 : $i, X20 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.89/1.09           = (k3_xboole_0 @ X19 @ X20))),
% 0.89/1.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.09  thf('15', plain,
% 0.89/1.09      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.89/1.09      inference('sup+', [status(thm)], ['13', '14'])).
% 0.89/1.09  thf(commutativity_k3_xboole_0, axiom,
% 0.89/1.09    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.89/1.09  thf('16', plain,
% 0.89/1.09      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.89/1.09      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.89/1.09  thf('17', plain,
% 0.89/1.09      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.89/1.09      inference('sup+', [status(thm)], ['15', '16'])).
% 0.89/1.09  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.89/1.09      inference('demod', [status(thm)], ['4', '17'])).
% 0.89/1.09  thf('19', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('20', plain,
% 0.89/1.09      (![X10 : $i, X11 : $i]:
% 0.89/1.09         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.89/1.09      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.89/1.09  thf('21', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.89/1.09      inference('sup-', [status(thm)], ['19', '20'])).
% 0.89/1.09  thf(t41_xboole_1, axiom,
% 0.89/1.09    (![A:$i,B:$i,C:$i]:
% 0.89/1.09     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.89/1.09       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.89/1.09  thf('22', plain,
% 0.89/1.09      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.89/1.09           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.89/1.09      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.89/1.09  thf('23', plain,
% 0.89/1.09      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.89/1.09      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.89/1.09  thf('24', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 0.89/1.09          (k4_xboole_0 @ X2 @ X1))),
% 0.89/1.09      inference('sup+', [status(thm)], ['22', '23'])).
% 0.89/1.09  thf('25', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ (k4_xboole_0 @ X0 @ sk_A))),
% 0.89/1.09      inference('sup+', [status(thm)], ['21', '24'])).
% 0.89/1.09  thf('26', plain,
% 0.89/1.09      (![X10 : $i, X11 : $i]:
% 0.89/1.09         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.89/1.09      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.89/1.09  thf('27', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ (k4_xboole_0 @ X0 @ sk_A))
% 0.89/1.09           = (k4_xboole_0 @ X0 @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['25', '26'])).
% 0.89/1.09  thf('28', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.09  thf('29', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_A) @ (k4_xboole_0 @ X0 @ sk_B))
% 0.89/1.09           = (k4_xboole_0 @ X0 @ sk_A))),
% 0.89/1.09      inference('demod', [status(thm)], ['27', '28'])).
% 0.89/1.09  thf('30', plain,
% 0.89/1.09      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.89/1.09         = (k4_xboole_0 @ sk_A @ sk_A))),
% 0.89/1.09      inference('sup+', [status(thm)], ['18', '29'])).
% 0.89/1.09  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.89/1.09      inference('sup+', [status(thm)], ['10', '11'])).
% 0.89/1.09  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.89/1.09      inference('demod', [status(thm)], ['4', '17'])).
% 0.89/1.09  thf('33', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.89/1.09      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.89/1.09  thf('34', plain,
% 0.89/1.09      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.89/1.09           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.89/1.09      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.89/1.09  thf('35', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.89/1.09           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['33', '34'])).
% 0.89/1.09  thf('36', plain,
% 0.89/1.09      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.89/1.09      inference('sup+', [status(thm)], ['9', '12'])).
% 0.89/1.09  thf('37', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.89/1.09      inference('demod', [status(thm)], ['35', '36'])).
% 0.89/1.09  thf('38', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['1', '37'])).
% 0.89/1.09  thf('39', plain,
% 0.89/1.09      (![X19 : $i, X20 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.89/1.09           = (k3_xboole_0 @ X19 @ X20))),
% 0.89/1.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.09  thf('40', plain,
% 0.89/1.09      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.89/1.09           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.89/1.09      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.89/1.09  thf('41', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.89/1.09           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['39', '40'])).
% 0.89/1.09  thf('42', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B) = (k1_xboole_0))),
% 0.89/1.09      inference('sup+', [status(thm)], ['38', '41'])).
% 0.89/1.09  thf('43', plain,
% 0.89/1.09      (![X19 : $i, X20 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.89/1.09           = (k3_xboole_0 @ X19 @ X20))),
% 0.89/1.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.09  thf('44', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ k1_xboole_0)
% 0.89/1.09           = (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.89/1.09      inference('sup+', [status(thm)], ['42', '43'])).
% 0.89/1.09  thf('45', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.89/1.09      inference('cnf', [status(esa)], [t3_boole])).
% 0.89/1.09  thf('46', plain,
% 0.89/1.09      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.89/1.09      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.89/1.09  thf('47', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((k3_xboole_0 @ sk_A @ X0)
% 0.89/1.09           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.89/1.09      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.89/1.09  thf('48', plain,
% 0.89/1.09      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.89/1.09      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.89/1.09  thf('49', plain,
% 0.89/1.09      (![X19 : $i, X20 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.89/1.09           = (k3_xboole_0 @ X19 @ X20))),
% 0.89/1.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.09  thf('50', plain,
% 0.89/1.09      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.89/1.09      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.89/1.09  thf('51', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.89/1.09      inference('sup+', [status(thm)], ['49', '50'])).
% 0.89/1.09  thf('52', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.89/1.09      inference('sup+', [status(thm)], ['48', '51'])).
% 0.89/1.09  thf('53', plain,
% 0.89/1.09      (![X10 : $i, X11 : $i]:
% 0.89/1.09         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.89/1.09      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.89/1.09  thf('54', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.89/1.09      inference('sup-', [status(thm)], ['52', '53'])).
% 0.89/1.09  thf('55', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.09  thf('56', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.89/1.09      inference('demod', [status(thm)], ['54', '55'])).
% 0.89/1.09  thf('57', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf(d7_xboole_0, axiom,
% 0.89/1.09    (![A:$i,B:$i]:
% 0.89/1.09     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.89/1.09       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.89/1.09  thf('58', plain,
% 0.89/1.09      (![X4 : $i, X5 : $i]:
% 0.89/1.09         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.89/1.09      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.89/1.09  thf('59', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.89/1.09      inference('sup-', [status(thm)], ['57', '58'])).
% 0.89/1.09  thf('60', plain,
% 0.89/1.09      (![X19 : $i, X20 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.89/1.09           = (k3_xboole_0 @ X19 @ X20))),
% 0.89/1.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.09  thf('61', plain,
% 0.89/1.09      (![X19 : $i, X20 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.89/1.09           = (k3_xboole_0 @ X19 @ X20))),
% 0.89/1.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.09  thf('62', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.89/1.09           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['60', '61'])).
% 0.89/1.09  thf('63', plain,
% 0.89/1.09      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 0.89/1.09         = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['59', '62'])).
% 0.89/1.09  thf('64', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.89/1.09      inference('cnf', [status(esa)], [t3_boole])).
% 0.89/1.09  thf('65', plain,
% 0.89/1.09      (((sk_B) = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.89/1.09      inference('demod', [status(thm)], ['63', '64'])).
% 0.89/1.09  thf('66', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.89/1.09      inference('demod', [status(thm)], ['54', '55'])).
% 0.89/1.09  thf('67', plain,
% 0.89/1.09      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_B)
% 0.89/1.09         = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.89/1.09      inference('sup+', [status(thm)], ['65', '66'])).
% 0.89/1.09  thf('68', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.09      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.09  thf('69', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.89/1.09      inference('demod', [status(thm)], ['7', '8'])).
% 0.89/1.09  thf('70', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.89/1.09      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.89/1.09  thf('71', plain,
% 0.89/1.09      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.89/1.09           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.89/1.09      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.89/1.09  thf('72', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ sk_B @ X0)
% 0.89/1.09           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['70', '71'])).
% 0.89/1.09  thf('73', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_C))
% 0.89/1.09           = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.89/1.09      inference('sup+', [status(thm)], ['56', '72'])).
% 0.89/1.09  thf('74', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.89/1.09      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.89/1.09  thf('75', plain,
% 0.89/1.09      (![X0 : $i]: ((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_C)) = (sk_B))),
% 0.89/1.09      inference('demod', [status(thm)], ['73', '74'])).
% 0.89/1.09  thf('76', plain,
% 0.89/1.09      (![X19 : $i, X20 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.89/1.09           = (k3_xboole_0 @ X19 @ X20))),
% 0.89/1.09      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.09  thf('77', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((k4_xboole_0 @ sk_B @ sk_B)
% 0.89/1.09           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_C)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['75', '76'])).
% 0.89/1.09  thf('78', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.89/1.09      inference('demod', [status(thm)], ['4', '17'])).
% 0.89/1.09  thf('79', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_C)))),
% 0.89/1.09      inference('demod', [status(thm)], ['77', '78'])).
% 0.89/1.09  thf('80', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.89/1.09      inference('sup+', [status(thm)], ['47', '79'])).
% 0.89/1.09  thf('81', plain,
% 0.89/1.09      (![X4 : $i, X6 : $i]:
% 0.89/1.09         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.89/1.09      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.89/1.09  thf('82', plain,
% 0.89/1.09      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C))),
% 0.89/1.09      inference('sup-', [status(thm)], ['80', '81'])).
% 0.89/1.09  thf('83', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.89/1.09      inference('simplify', [status(thm)], ['82'])).
% 0.89/1.09  thf('84', plain, ($false), inference('demod', [status(thm)], ['0', '83'])).
% 0.89/1.09  
% 0.89/1.09  % SZS output end Refutation
% 0.89/1.09  
% 0.89/1.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
