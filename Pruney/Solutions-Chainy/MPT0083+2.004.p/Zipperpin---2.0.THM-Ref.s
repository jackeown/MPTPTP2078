%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lougCqLgzZ

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:16 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 123 expanded)
%              Number of leaves         :   22 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  636 ( 874 expanded)
%              Number of equality atoms :   69 (  98 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t76_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('14',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('17',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['18','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['15','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = sk_B ) ),
    inference('sup+',[status(thm)],['4','26'])).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('49',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('54',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('61',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['3','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lougCqLgzZ
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.01/1.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.01/1.21  % Solved by: fo/fo7.sh
% 1.01/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.01/1.21  % done 1904 iterations in 0.744s
% 1.01/1.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.01/1.21  % SZS output start Refutation
% 1.01/1.21  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.01/1.21  thf(sk_C_type, type, sk_C: $i).
% 1.01/1.21  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.01/1.21  thf(sk_A_type, type, sk_A: $i).
% 1.01/1.21  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.01/1.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.01/1.21  thf(sk_B_type, type, sk_B: $i).
% 1.01/1.21  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.01/1.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.01/1.21  thf(t76_xboole_1, conjecture,
% 1.01/1.21    (![A:$i,B:$i,C:$i]:
% 1.01/1.21     ( ( r1_xboole_0 @ A @ B ) =>
% 1.01/1.21       ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ))).
% 1.01/1.21  thf(zf_stmt_0, negated_conjecture,
% 1.01/1.21    (~( ![A:$i,B:$i,C:$i]:
% 1.01/1.21        ( ( r1_xboole_0 @ A @ B ) =>
% 1.01/1.21          ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )),
% 1.01/1.21    inference('cnf.neg', [status(esa)], [t76_xboole_1])).
% 1.01/1.21  thf('0', plain,
% 1.01/1.21      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 1.01/1.21          (k3_xboole_0 @ sk_C @ sk_B))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf(commutativity_k3_xboole_0, axiom,
% 1.01/1.21    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.01/1.21  thf('1', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.01/1.21      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.01/1.21  thf('2', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.01/1.21      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.01/1.21  thf('3', plain,
% 1.01/1.21      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 1.01/1.21          (k3_xboole_0 @ sk_B @ sk_C))),
% 1.01/1.21      inference('demod', [status(thm)], ['0', '1', '2'])).
% 1.01/1.21  thf(t48_xboole_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.01/1.21  thf('4', plain,
% 1.01/1.21      (![X19 : $i, X20 : $i]:
% 1.01/1.21         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 1.01/1.21           = (k3_xboole_0 @ X19 @ X20))),
% 1.01/1.21      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.01/1.21  thf('5', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf(d7_xboole_0, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.01/1.21       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.01/1.21  thf('6', plain,
% 1.01/1.21      (![X2 : $i, X3 : $i]:
% 1.01/1.21         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.01/1.21      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.01/1.21  thf('7', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 1.01/1.21      inference('sup-', [status(thm)], ['5', '6'])).
% 1.01/1.21  thf('8', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.01/1.21      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.01/1.21  thf(t47_xboole_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.01/1.21  thf('9', plain,
% 1.01/1.21      (![X17 : $i, X18 : $i]:
% 1.01/1.21         ((k4_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18))
% 1.01/1.21           = (k4_xboole_0 @ X17 @ X18))),
% 1.01/1.21      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.01/1.21  thf('10', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.01/1.21           = (k4_xboole_0 @ X0 @ X1))),
% 1.01/1.21      inference('sup+', [status(thm)], ['8', '9'])).
% 1.01/1.21  thf('11', plain,
% 1.01/1.21      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_A))),
% 1.01/1.21      inference('sup+', [status(thm)], ['7', '10'])).
% 1.01/1.21  thf(t3_boole, axiom,
% 1.01/1.21    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.01/1.21  thf('12', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.01/1.21      inference('cnf', [status(esa)], [t3_boole])).
% 1.01/1.21  thf('13', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 1.01/1.21      inference('demod', [status(thm)], ['11', '12'])).
% 1.01/1.21  thf(t52_xboole_1, axiom,
% 1.01/1.21    (![A:$i,B:$i,C:$i]:
% 1.01/1.21     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.01/1.21       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 1.01/1.21  thf('14', plain,
% 1.01/1.21      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.01/1.21         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 1.01/1.21           = (k2_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ 
% 1.01/1.21              (k3_xboole_0 @ X23 @ X25)))),
% 1.01/1.21      inference('cnf', [status(esa)], [t52_xboole_1])).
% 1.01/1.21  thf('15', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0))
% 1.01/1.21           = (k2_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ X0)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['13', '14'])).
% 1.01/1.21  thf('16', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.01/1.21      inference('cnf', [status(esa)], [t3_boole])).
% 1.01/1.21  thf('17', plain,
% 1.01/1.21      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.01/1.21         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 1.01/1.21           = (k2_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ 
% 1.01/1.21              (k3_xboole_0 @ X23 @ X25)))),
% 1.01/1.21      inference('cnf', [status(esa)], [t52_xboole_1])).
% 1.01/1.21  thf('18', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1))
% 1.01/1.21           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['16', '17'])).
% 1.01/1.21  thf(t2_boole, axiom,
% 1.01/1.21    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.01/1.21  thf('19', plain,
% 1.01/1.21      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.01/1.21      inference('cnf', [status(esa)], [t2_boole])).
% 1.01/1.21  thf(t17_xboole_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.01/1.21  thf('20', plain,
% 1.01/1.21      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 1.01/1.21      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.01/1.21  thf('21', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.01/1.21      inference('sup+', [status(thm)], ['19', '20'])).
% 1.01/1.21  thf(l32_xboole_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.01/1.21  thf('22', plain,
% 1.01/1.21      (![X5 : $i, X7 : $i]:
% 1.01/1.21         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.01/1.21      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.01/1.21  thf('23', plain,
% 1.01/1.21      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.01/1.21      inference('sup-', [status(thm)], ['21', '22'])).
% 1.01/1.21  thf('24', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.01/1.21      inference('cnf', [status(esa)], [t3_boole])).
% 1.01/1.21  thf('25', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.01/1.21      inference('demod', [status(thm)], ['18', '23', '24'])).
% 1.01/1.21  thf('26', plain,
% 1.01/1.21      (![X0 : $i]: ((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0)) = (sk_B))),
% 1.01/1.21      inference('demod', [status(thm)], ['15', '25'])).
% 1.01/1.21  thf('27', plain,
% 1.01/1.21      (![X0 : $i]: ((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)) = (sk_B))),
% 1.01/1.21      inference('sup+', [status(thm)], ['4', '26'])).
% 1.01/1.21  thf('28', plain,
% 1.01/1.21      (![X19 : $i, X20 : $i]:
% 1.01/1.21         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 1.01/1.21           = (k3_xboole_0 @ X19 @ X20))),
% 1.01/1.21      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.01/1.21  thf('29', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((k4_xboole_0 @ sk_B @ sk_B)
% 1.01/1.21           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['27', '28'])).
% 1.01/1.21  thf('30', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.01/1.21      inference('cnf', [status(esa)], [t3_boole])).
% 1.01/1.21  thf('31', plain,
% 1.01/1.21      (![X19 : $i, X20 : $i]:
% 1.01/1.21         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 1.01/1.21           = (k3_xboole_0 @ X19 @ X20))),
% 1.01/1.21      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.01/1.21  thf('32', plain,
% 1.01/1.21      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.01/1.21      inference('sup+', [status(thm)], ['30', '31'])).
% 1.01/1.21  thf('33', plain,
% 1.01/1.21      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.01/1.21      inference('cnf', [status(esa)], [t2_boole])).
% 1.01/1.21  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.01/1.21      inference('demod', [status(thm)], ['32', '33'])).
% 1.01/1.21  thf('35', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 1.01/1.21      inference('demod', [status(thm)], ['29', '34'])).
% 1.01/1.21  thf('36', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.01/1.21           = (k4_xboole_0 @ X0 @ X1))),
% 1.01/1.21      inference('sup+', [status(thm)], ['8', '9'])).
% 1.01/1.21  thf('37', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ k1_xboole_0)
% 1.01/1.21           = (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B))),
% 1.01/1.21      inference('sup+', [status(thm)], ['35', '36'])).
% 1.01/1.21  thf('38', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.01/1.21      inference('cnf', [status(esa)], [t3_boole])).
% 1.01/1.21  thf('39', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((k3_xboole_0 @ sk_A @ X0)
% 1.01/1.21           = (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B))),
% 1.01/1.21      inference('demod', [status(thm)], ['37', '38'])).
% 1.01/1.21  thf('40', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.01/1.21      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.01/1.21  thf('41', plain,
% 1.01/1.21      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.01/1.21         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 1.01/1.21           = (k2_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ 
% 1.01/1.21              (k3_xboole_0 @ X23 @ X25)))),
% 1.01/1.21      inference('cnf', [status(esa)], [t52_xboole_1])).
% 1.01/1.21  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.01/1.21      inference('demod', [status(thm)], ['32', '33'])).
% 1.01/1.21  thf(t41_xboole_1, axiom,
% 1.01/1.21    (![A:$i,B:$i,C:$i]:
% 1.01/1.21     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.01/1.21       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.01/1.21  thf('43', plain,
% 1.01/1.21      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.01/1.21         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 1.01/1.21           = (k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 1.01/1.21      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.01/1.21  thf('44', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k1_xboole_0)
% 1.01/1.21           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.01/1.21      inference('sup+', [status(thm)], ['42', '43'])).
% 1.01/1.21  thf(t39_xboole_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.01/1.21  thf('45', plain,
% 1.01/1.21      (![X11 : $i, X12 : $i]:
% 1.01/1.21         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 1.01/1.21           = (k2_xboole_0 @ X11 @ X12))),
% 1.01/1.21      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.01/1.21  thf('46', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.01/1.21      inference('demod', [status(thm)], ['44', '45'])).
% 1.01/1.21  thf('47', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         ((k1_xboole_0)
% 1.01/1.21           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ 
% 1.01/1.21              (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.01/1.21      inference('sup+', [status(thm)], ['41', '46'])).
% 1.01/1.21  thf('48', plain,
% 1.01/1.21      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 1.01/1.21      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.01/1.21  thf('49', plain,
% 1.01/1.21      (![X5 : $i, X7 : $i]:
% 1.01/1.21         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.01/1.21      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.01/1.21  thf('50', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.01/1.21      inference('sup-', [status(thm)], ['48', '49'])).
% 1.01/1.21  thf('51', plain,
% 1.01/1.21      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.01/1.21         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 1.01/1.21           = (k2_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ 
% 1.01/1.21              (k3_xboole_0 @ X23 @ X25)))),
% 1.01/1.21      inference('cnf', [status(esa)], [t52_xboole_1])).
% 1.01/1.21  thf('52', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X2 @ X0))
% 1.01/1.21           = (k2_xboole_0 @ k1_xboole_0 @ 
% 1.01/1.21              (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 1.01/1.21      inference('sup+', [status(thm)], ['50', '51'])).
% 1.01/1.21  thf('53', plain,
% 1.01/1.21      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.01/1.21      inference('cnf', [status(esa)], [t2_boole])).
% 1.01/1.21  thf(t51_xboole_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.01/1.21       ( A ) ))).
% 1.01/1.21  thf('54', plain,
% 1.01/1.21      (![X21 : $i, X22 : $i]:
% 1.01/1.21         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 1.01/1.21           = (X21))),
% 1.01/1.21      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.01/1.21  thf('55', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 1.01/1.21      inference('sup+', [status(thm)], ['53', '54'])).
% 1.01/1.21  thf('56', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.01/1.21      inference('cnf', [status(esa)], [t3_boole])).
% 1.01/1.21  thf('57', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.01/1.21      inference('demod', [status(thm)], ['55', '56'])).
% 1.01/1.21  thf('58', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X2 @ X0))
% 1.01/1.21           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.01/1.21      inference('demod', [status(thm)], ['52', '57'])).
% 1.01/1.21  thf('59', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         ((k1_xboole_0)
% 1.01/1.21           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.01/1.21      inference('demod', [status(thm)], ['47', '58'])).
% 1.01/1.21  thf('60', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.01/1.21      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.01/1.21  thf('61', plain,
% 1.01/1.21      (![X2 : $i, X4 : $i]:
% 1.01/1.21         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.01/1.21      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.01/1.21  thf('62', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 1.01/1.21      inference('sup-', [status(thm)], ['60', '61'])).
% 1.01/1.21  thf('63', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         (((k1_xboole_0) != (k1_xboole_0))
% 1.01/1.21          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X0)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['59', '62'])).
% 1.01/1.21  thf('64', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X0))),
% 1.01/1.21      inference('simplify', [status(thm)], ['63'])).
% 1.01/1.21  thf('65', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X0))),
% 1.01/1.21      inference('sup+', [status(thm)], ['40', '64'])).
% 1.01/1.21  thf('66', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ (k3_xboole_0 @ sk_B @ X1))),
% 1.01/1.21      inference('sup+', [status(thm)], ['39', '65'])).
% 1.01/1.21  thf('67', plain, ($false), inference('demod', [status(thm)], ['3', '66'])).
% 1.01/1.21  
% 1.01/1.21  % SZS output end Refutation
% 1.01/1.21  
% 1.01/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
