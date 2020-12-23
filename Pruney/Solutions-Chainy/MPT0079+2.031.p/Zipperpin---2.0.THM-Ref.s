%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9Jf6twjkO5

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:01 EST 2020

% Result     : Theorem 1.12s
% Output     : Refutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :  157 (1411 expanded)
%              Number of leaves         :   26 ( 478 expanded)
%              Depth                    :   31
%              Number of atoms          : 1124 (11589 expanded)
%              Number of equality atoms :  139 (1430 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t72_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ D ) )
          & ( r1_xboole_0 @ C @ A )
          & ( r1_xboole_0 @ D @ B ) )
       => ( C = B ) ) ),
    inference('cnf.neg',[status(esa)],[t72_xboole_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
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

thf('2',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('4',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_C @ sk_D ) )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_D )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('13',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ X32 @ ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('23',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('25',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('28',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','29'])).

thf('31',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('36',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['30','37'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('39',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k2_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ X0 )
      = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ X0 )
      = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['3','40'])).

thf('42',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_C )
    = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('48',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','46','47'])).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('50',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_A )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('52',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('56',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('58',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['50','51','58'])).

thf('60',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('61',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['50','51','58'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('64',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ X32 @ ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['62','75'])).

thf('77',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['50','51','58'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = sk_C ) ),
    inference('sup+',[status(thm)],['61','78'])).

thf('80',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('81',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k4_xboole_0 @ X25 @ X26 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('85',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ ( k3_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['79','86'])).

thf('88',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('89',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('95',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('97',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_D @ sk_A ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_A @ sk_D ) ) ),
    inference('sup+',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('101',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['30','37'])).

thf('102',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('103',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['93','94'])).

thf('104',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('105',plain,(
    sk_A = sk_D ),
    inference(demod,[status(thm)],['99','100','101','102','103','104'])).

thf('106',plain,(
    sk_A = sk_D ),
    inference(demod,[status(thm)],['99','100','101','102','103','104'])).

thf('107',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['60','105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('109',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('110',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('114',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ X32 @ ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['112','117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('123',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['121','124'])).

thf('126',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['107','125'])).

thf('127',plain,(
    sk_C = sk_B ),
    inference('sup+',[status(thm)],['59','126'])).

thf('128',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['127','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9Jf6twjkO5
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:26:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.12/1.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.12/1.34  % Solved by: fo/fo7.sh
% 1.12/1.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.12/1.34  % done 1752 iterations in 0.882s
% 1.12/1.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.12/1.34  % SZS output start Refutation
% 1.12/1.34  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.12/1.34  thf(sk_A_type, type, sk_A: $i).
% 1.12/1.34  thf(sk_D_type, type, sk_D: $i).
% 1.12/1.34  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.12/1.34  thf(sk_C_type, type, sk_C: $i).
% 1.12/1.34  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.12/1.34  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.12/1.34  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.12/1.34  thf(sk_B_type, type, sk_B: $i).
% 1.12/1.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.12/1.34  thf(t72_xboole_1, conjecture,
% 1.12/1.34    (![A:$i,B:$i,C:$i,D:$i]:
% 1.12/1.34     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 1.12/1.34         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 1.12/1.34       ( ( C ) = ( B ) ) ))).
% 1.12/1.34  thf(zf_stmt_0, negated_conjecture,
% 1.12/1.34    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.12/1.34        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 1.12/1.34            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 1.12/1.34          ( ( C ) = ( B ) ) ) )),
% 1.12/1.34    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 1.12/1.34  thf('0', plain,
% 1.12/1.34      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf(commutativity_k2_xboole_0, axiom,
% 1.12/1.34    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.12/1.34  thf('1', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.12/1.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.12/1.34  thf('2', plain,
% 1.12/1.34      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.12/1.34      inference('demod', [status(thm)], ['0', '1'])).
% 1.12/1.34  thf('3', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.12/1.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.12/1.34  thf('4', plain,
% 1.12/1.34      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.12/1.34      inference('demod', [status(thm)], ['0', '1'])).
% 1.12/1.34  thf(t40_xboole_1, axiom,
% 1.12/1.34    (![A:$i,B:$i]:
% 1.12/1.34     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.12/1.34  thf('5', plain,
% 1.12/1.34      (![X13 : $i, X14 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 1.12/1.34           = (k4_xboole_0 @ X13 @ X14))),
% 1.12/1.34      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.12/1.34  thf('6', plain,
% 1.12/1.34      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 1.12/1.34         = (k4_xboole_0 @ sk_C @ sk_D))),
% 1.12/1.34      inference('sup+', [status(thm)], ['4', '5'])).
% 1.12/1.34  thf(t39_xboole_1, axiom,
% 1.12/1.34    (![A:$i,B:$i]:
% 1.12/1.34     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.12/1.34  thf('7', plain,
% 1.12/1.34      (![X10 : $i, X11 : $i]:
% 1.12/1.34         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.12/1.34           = (k2_xboole_0 @ X10 @ X11))),
% 1.12/1.34      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.12/1.34  thf('8', plain,
% 1.12/1.34      (((k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_C @ sk_D))
% 1.12/1.34         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.12/1.34      inference('sup+', [status(thm)], ['6', '7'])).
% 1.12/1.34  thf('9', plain,
% 1.12/1.34      (![X10 : $i, X11 : $i]:
% 1.12/1.34         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.12/1.34           = (k2_xboole_0 @ X10 @ X11))),
% 1.12/1.34      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.12/1.34  thf('10', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.12/1.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.12/1.34  thf('11', plain,
% 1.12/1.34      (((k2_xboole_0 @ sk_C @ sk_D)
% 1.12/1.34         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.12/1.34      inference('demod', [status(thm)], ['8', '9', '10'])).
% 1.12/1.34  thf('12', plain,
% 1.12/1.34      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.12/1.34      inference('demod', [status(thm)], ['0', '1'])).
% 1.12/1.34  thf('13', plain,
% 1.12/1.34      (((k2_xboole_0 @ sk_B @ sk_A)
% 1.12/1.34         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.12/1.34      inference('demod', [status(thm)], ['11', '12'])).
% 1.12/1.34  thf('14', plain,
% 1.12/1.34      (![X13 : $i, X14 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 1.12/1.34           = (k4_xboole_0 @ X13 @ X14))),
% 1.12/1.34      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.12/1.34  thf('15', plain,
% 1.12/1.34      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ 
% 1.12/1.34         (k2_xboole_0 @ sk_B @ sk_A))
% 1.12/1.34         = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.12/1.34      inference('sup+', [status(thm)], ['13', '14'])).
% 1.12/1.34  thf(t1_boole, axiom,
% 1.12/1.34    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.12/1.34  thf('16', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 1.12/1.34      inference('cnf', [status(esa)], [t1_boole])).
% 1.12/1.34  thf(t7_xboole_1, axiom,
% 1.12/1.34    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.12/1.34  thf('17', plain,
% 1.12/1.34      (![X32 : $i, X33 : $i]: (r1_tarski @ X32 @ (k2_xboole_0 @ X32 @ X33))),
% 1.12/1.34      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.12/1.34  thf('18', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.12/1.34      inference('sup+', [status(thm)], ['16', '17'])).
% 1.12/1.34  thf(l32_xboole_1, axiom,
% 1.12/1.34    (![A:$i,B:$i]:
% 1.12/1.34     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.12/1.34  thf('19', plain,
% 1.12/1.34      (![X5 : $i, X7 : $i]:
% 1.12/1.34         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.12/1.34      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.12/1.34  thf('20', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.12/1.34      inference('sup-', [status(thm)], ['18', '19'])).
% 1.12/1.34  thf('21', plain,
% 1.12/1.34      (((k1_xboole_0) = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.12/1.34      inference('demod', [status(thm)], ['15', '20'])).
% 1.12/1.34  thf(t41_xboole_1, axiom,
% 1.12/1.34    (![A:$i,B:$i,C:$i]:
% 1.12/1.34     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.12/1.34       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.12/1.34  thf('22', plain,
% 1.12/1.34      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 1.12/1.34           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 1.12/1.34      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.12/1.34  thf('23', plain,
% 1.12/1.34      (((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A))),
% 1.12/1.34      inference('demod', [status(thm)], ['21', '22'])).
% 1.12/1.34  thf('24', plain,
% 1.12/1.34      (![X10 : $i, X11 : $i]:
% 1.12/1.34         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.12/1.34           = (k2_xboole_0 @ X10 @ X11))),
% 1.12/1.34      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.12/1.34  thf('25', plain,
% 1.12/1.34      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 1.12/1.34         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)))),
% 1.12/1.34      inference('sup+', [status(thm)], ['23', '24'])).
% 1.12/1.34  thf('26', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.12/1.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.12/1.34  thf('27', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.12/1.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.12/1.34  thf('28', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 1.12/1.34      inference('cnf', [status(esa)], [t1_boole])).
% 1.12/1.34  thf('29', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.12/1.34      inference('sup+', [status(thm)], ['27', '28'])).
% 1.12/1.34  thf('30', plain,
% 1.12/1.34      (((sk_A) = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)))),
% 1.12/1.34      inference('demod', [status(thm)], ['25', '26', '29'])).
% 1.12/1.34  thf('31', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf(d7_xboole_0, axiom,
% 1.12/1.34    (![A:$i,B:$i]:
% 1.12/1.34     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.12/1.34       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.12/1.34  thf('32', plain,
% 1.12/1.34      (![X2 : $i, X3 : $i]:
% 1.12/1.34         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.12/1.34      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.12/1.34  thf('33', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 1.12/1.34      inference('sup-', [status(thm)], ['31', '32'])).
% 1.12/1.34  thf(t47_xboole_1, axiom,
% 1.12/1.34    (![A:$i,B:$i]:
% 1.12/1.34     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.12/1.34  thf('34', plain,
% 1.12/1.34      (![X18 : $i, X19 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 1.12/1.34           = (k4_xboole_0 @ X18 @ X19))),
% 1.12/1.34      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.12/1.34  thf('35', plain,
% 1.12/1.34      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_B))),
% 1.12/1.34      inference('sup+', [status(thm)], ['33', '34'])).
% 1.12/1.34  thf(t3_boole, axiom,
% 1.12/1.34    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.12/1.34  thf('36', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.12/1.34      inference('cnf', [status(esa)], [t3_boole])).
% 1.12/1.34  thf('37', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B))),
% 1.12/1.34      inference('demod', [status(thm)], ['35', '36'])).
% 1.12/1.34  thf('38', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 1.12/1.34      inference('demod', [status(thm)], ['30', '37'])).
% 1.12/1.34  thf(t4_xboole_1, axiom,
% 1.12/1.34    (![A:$i,B:$i,C:$i]:
% 1.12/1.34     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 1.12/1.34       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.12/1.34  thf('39', plain,
% 1.12/1.34      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.12/1.34         ((k2_xboole_0 @ (k2_xboole_0 @ X22 @ X23) @ X24)
% 1.12/1.34           = (k2_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 1.12/1.34      inference('cnf', [status(esa)], [t4_xboole_1])).
% 1.12/1.34  thf('40', plain,
% 1.12/1.34      (![X0 : $i]:
% 1.12/1.34         ((k2_xboole_0 @ sk_A @ X0)
% 1.12/1.34           = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_D @ X0)))),
% 1.12/1.34      inference('sup+', [status(thm)], ['38', '39'])).
% 1.12/1.34  thf('41', plain,
% 1.12/1.34      (![X0 : $i]:
% 1.12/1.34         ((k2_xboole_0 @ sk_A @ X0)
% 1.12/1.34           = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_D)))),
% 1.12/1.34      inference('sup+', [status(thm)], ['3', '40'])).
% 1.12/1.34  thf('42', plain,
% 1.12/1.34      (((k2_xboole_0 @ sk_A @ sk_C)
% 1.12/1.34         = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.12/1.34      inference('sup+', [status(thm)], ['2', '41'])).
% 1.12/1.34  thf('43', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.12/1.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.12/1.34  thf('44', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.12/1.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.12/1.34  thf(t6_xboole_1, axiom,
% 1.12/1.34    (![A:$i,B:$i]:
% 1.12/1.34     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.12/1.34  thf('45', plain,
% 1.12/1.34      (![X30 : $i, X31 : $i]:
% 1.12/1.34         ((k2_xboole_0 @ X30 @ (k2_xboole_0 @ X30 @ X31))
% 1.12/1.34           = (k2_xboole_0 @ X30 @ X31))),
% 1.12/1.34      inference('cnf', [status(esa)], [t6_xboole_1])).
% 1.12/1.34  thf('46', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.12/1.34           = (k2_xboole_0 @ X0 @ X1))),
% 1.12/1.34      inference('sup+', [status(thm)], ['44', '45'])).
% 1.12/1.34  thf('47', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.12/1.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.12/1.34  thf('48', plain,
% 1.12/1.34      (((k2_xboole_0 @ sk_C @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 1.12/1.34      inference('demod', [status(thm)], ['42', '43', '46', '47'])).
% 1.12/1.34  thf('49', plain,
% 1.12/1.34      (![X13 : $i, X14 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 1.12/1.34           = (k4_xboole_0 @ X13 @ X14))),
% 1.12/1.34      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.12/1.34  thf('50', plain,
% 1.12/1.34      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_A)
% 1.12/1.34         = (k4_xboole_0 @ sk_C @ sk_A))),
% 1.12/1.34      inference('sup+', [status(thm)], ['48', '49'])).
% 1.12/1.34  thf('51', plain,
% 1.12/1.34      (![X13 : $i, X14 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 1.12/1.34           = (k4_xboole_0 @ X13 @ X14))),
% 1.12/1.34      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.12/1.34  thf('52', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('53', plain,
% 1.12/1.34      (![X2 : $i, X3 : $i]:
% 1.12/1.34         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.12/1.34      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.12/1.34  thf('54', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 1.12/1.34      inference('sup-', [status(thm)], ['52', '53'])).
% 1.12/1.34  thf('55', plain,
% 1.12/1.34      (![X18 : $i, X19 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 1.12/1.34           = (k4_xboole_0 @ X18 @ X19))),
% 1.12/1.34      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.12/1.34  thf('56', plain,
% 1.12/1.34      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_A))),
% 1.12/1.34      inference('sup+', [status(thm)], ['54', '55'])).
% 1.12/1.34  thf('57', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.12/1.34      inference('cnf', [status(esa)], [t3_boole])).
% 1.12/1.34  thf('58', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 1.12/1.34      inference('demod', [status(thm)], ['56', '57'])).
% 1.12/1.34  thf('59', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_C))),
% 1.12/1.34      inference('demod', [status(thm)], ['50', '51', '58'])).
% 1.12/1.34  thf('60', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B))),
% 1.12/1.34      inference('demod', [status(thm)], ['35', '36'])).
% 1.12/1.34  thf(t48_xboole_1, axiom,
% 1.12/1.34    (![A:$i,B:$i]:
% 1.12/1.34     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.12/1.34  thf('61', plain,
% 1.12/1.34      (![X20 : $i, X21 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.12/1.34           = (k3_xboole_0 @ X20 @ X21))),
% 1.12/1.34      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.12/1.34  thf('62', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_C))),
% 1.12/1.34      inference('demod', [status(thm)], ['50', '51', '58'])).
% 1.12/1.34  thf('63', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.12/1.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.12/1.34  thf('64', plain,
% 1.12/1.34      (![X32 : $i, X33 : $i]: (r1_tarski @ X32 @ (k2_xboole_0 @ X32 @ X33))),
% 1.12/1.34      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.12/1.34  thf('65', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.12/1.34      inference('sup+', [status(thm)], ['63', '64'])).
% 1.12/1.34  thf('66', plain,
% 1.12/1.34      (![X5 : $i, X7 : $i]:
% 1.12/1.34         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.12/1.34      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.12/1.34  thf('67', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.12/1.34      inference('sup-', [status(thm)], ['65', '66'])).
% 1.12/1.34  thf('68', plain,
% 1.12/1.34      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 1.12/1.34           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 1.12/1.34      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.12/1.34  thf('69', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.12/1.34      inference('demod', [status(thm)], ['67', '68'])).
% 1.12/1.34  thf('70', plain,
% 1.12/1.34      (![X10 : $i, X11 : $i]:
% 1.12/1.34         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.12/1.34           = (k2_xboole_0 @ X10 @ X11))),
% 1.12/1.34      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.12/1.34  thf('71', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 1.12/1.34           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.12/1.34      inference('sup+', [status(thm)], ['69', '70'])).
% 1.12/1.34  thf('72', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 1.12/1.34      inference('cnf', [status(esa)], [t1_boole])).
% 1.12/1.34  thf('73', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.12/1.34      inference('demod', [status(thm)], ['71', '72'])).
% 1.12/1.34  thf('74', plain,
% 1.12/1.34      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 1.12/1.34           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 1.12/1.34      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.12/1.34  thf('75', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 1.12/1.34           = (k4_xboole_0 @ X2 @ X0))),
% 1.12/1.34      inference('sup+', [status(thm)], ['73', '74'])).
% 1.12/1.34  thf('76', plain,
% 1.12/1.34      (![X0 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ X0))
% 1.12/1.34           = (k4_xboole_0 @ sk_B @ sk_A))),
% 1.12/1.34      inference('sup+', [status(thm)], ['62', '75'])).
% 1.12/1.34  thf('77', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_C))),
% 1.12/1.34      inference('demod', [status(thm)], ['50', '51', '58'])).
% 1.12/1.34  thf('78', plain,
% 1.12/1.34      (![X0 : $i]: ((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ X0)) = (sk_C))),
% 1.12/1.34      inference('demod', [status(thm)], ['76', '77'])).
% 1.12/1.34  thf('79', plain,
% 1.12/1.34      (![X0 : $i]: ((k4_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ X0)) = (sk_C))),
% 1.12/1.34      inference('sup+', [status(thm)], ['61', '78'])).
% 1.12/1.34  thf('80', plain,
% 1.12/1.34      (![X18 : $i, X19 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 1.12/1.34           = (k4_xboole_0 @ X18 @ X19))),
% 1.12/1.34      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.12/1.34  thf(t51_xboole_1, axiom,
% 1.12/1.34    (![A:$i,B:$i]:
% 1.12/1.34     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.12/1.34       ( A ) ))).
% 1.12/1.34  thf('81', plain,
% 1.12/1.34      (![X25 : $i, X26 : $i]:
% 1.12/1.34         ((k2_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ (k4_xboole_0 @ X25 @ X26))
% 1.12/1.34           = (X25))),
% 1.12/1.34      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.12/1.34  thf('82', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.12/1.34           (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 1.12/1.34      inference('sup+', [status(thm)], ['80', '81'])).
% 1.12/1.34  thf('83', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.12/1.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.12/1.34  thf('84', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 1.12/1.34           (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))) = (X1))),
% 1.12/1.34      inference('demod', [status(thm)], ['82', '83'])).
% 1.12/1.34  thf(t52_xboole_1, axiom,
% 1.12/1.34    (![A:$i,B:$i,C:$i]:
% 1.12/1.34     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.12/1.34       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 1.12/1.34  thf('85', plain,
% 1.12/1.34      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X29))
% 1.12/1.34           = (k2_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ 
% 1.12/1.34              (k3_xboole_0 @ X27 @ X29)))),
% 1.12/1.34      inference('cnf', [status(esa)], [t52_xboole_1])).
% 1.12/1.34  thf('86', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 1.12/1.34           = (X1))),
% 1.12/1.34      inference('demod', [status(thm)], ['84', '85'])).
% 1.12/1.34  thf('87', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 1.12/1.34      inference('sup+', [status(thm)], ['79', '86'])).
% 1.12/1.34  thf('88', plain,
% 1.12/1.34      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.12/1.34      inference('demod', [status(thm)], ['0', '1'])).
% 1.12/1.34  thf('89', plain,
% 1.12/1.34      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 1.12/1.34           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 1.12/1.34      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.12/1.34  thf('90', plain,
% 1.12/1.34      (![X0 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 1.12/1.34           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.12/1.34      inference('sup+', [status(thm)], ['88', '89'])).
% 1.12/1.34  thf('91', plain,
% 1.12/1.34      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 1.12/1.34           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 1.12/1.34      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.12/1.34  thf('92', plain,
% 1.12/1.34      (![X0 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 1.12/1.34           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 1.12/1.34      inference('demod', [status(thm)], ['90', '91'])).
% 1.12/1.34  thf('93', plain,
% 1.12/1.34      (((k4_xboole_0 @ sk_A @ sk_D)
% 1.12/1.34         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 1.12/1.34      inference('sup+', [status(thm)], ['87', '92'])).
% 1.12/1.34  thf('94', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.12/1.34      inference('demod', [status(thm)], ['67', '68'])).
% 1.12/1.34  thf('95', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 1.12/1.34      inference('demod', [status(thm)], ['93', '94'])).
% 1.12/1.34  thf('96', plain,
% 1.12/1.34      (![X10 : $i, X11 : $i]:
% 1.12/1.34         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.12/1.34           = (k2_xboole_0 @ X10 @ X11))),
% 1.12/1.34      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.12/1.34  thf('97', plain,
% 1.12/1.34      (![X13 : $i, X14 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 1.12/1.34           = (k4_xboole_0 @ X13 @ X14))),
% 1.12/1.34      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.12/1.34  thf('98', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 1.12/1.34           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.12/1.34      inference('sup+', [status(thm)], ['96', '97'])).
% 1.12/1.34  thf('99', plain,
% 1.12/1.34      (((k4_xboole_0 @ (k2_xboole_0 @ sk_D @ sk_A) @ k1_xboole_0)
% 1.12/1.34         = (k4_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_A @ sk_D)))),
% 1.12/1.34      inference('sup+', [status(thm)], ['95', '98'])).
% 1.12/1.34  thf('100', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.12/1.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.12/1.34  thf('101', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 1.12/1.34      inference('demod', [status(thm)], ['30', '37'])).
% 1.12/1.34  thf('102', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.12/1.34      inference('cnf', [status(esa)], [t3_boole])).
% 1.12/1.34  thf('103', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 1.12/1.34      inference('demod', [status(thm)], ['93', '94'])).
% 1.12/1.34  thf('104', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.12/1.34      inference('cnf', [status(esa)], [t3_boole])).
% 1.12/1.34  thf('105', plain, (((sk_A) = (sk_D))),
% 1.12/1.34      inference('demod', [status(thm)],
% 1.12/1.34                ['99', '100', '101', '102', '103', '104'])).
% 1.12/1.34  thf('106', plain, (((sk_A) = (sk_D))),
% 1.12/1.34      inference('demod', [status(thm)],
% 1.12/1.34                ['99', '100', '101', '102', '103', '104'])).
% 1.12/1.34  thf('107', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.12/1.34      inference('demod', [status(thm)], ['60', '105', '106'])).
% 1.12/1.34  thf('108', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.12/1.34      inference('sup-', [status(thm)], ['18', '19'])).
% 1.12/1.34  thf('109', plain,
% 1.12/1.34      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 1.12/1.34           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 1.12/1.34      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.12/1.34  thf('110', plain,
% 1.12/1.34      (![X20 : $i, X21 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.12/1.34           = (k3_xboole_0 @ X20 @ X21))),
% 1.12/1.34      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.12/1.34  thf('111', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 1.12/1.34           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.12/1.34      inference('sup+', [status(thm)], ['109', '110'])).
% 1.12/1.34  thf('112', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 1.12/1.34           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.12/1.34      inference('sup+', [status(thm)], ['108', '111'])).
% 1.12/1.34  thf('113', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.12/1.34      inference('sup+', [status(thm)], ['27', '28'])).
% 1.12/1.34  thf('114', plain,
% 1.12/1.34      (![X32 : $i, X33 : $i]: (r1_tarski @ X32 @ (k2_xboole_0 @ X32 @ X33))),
% 1.12/1.34      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.12/1.34  thf('115', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.12/1.34      inference('sup+', [status(thm)], ['113', '114'])).
% 1.12/1.34  thf('116', plain,
% 1.12/1.34      (![X5 : $i, X7 : $i]:
% 1.12/1.34         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.12/1.34      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.12/1.34  thf('117', plain,
% 1.12/1.34      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.12/1.34      inference('sup-', [status(thm)], ['115', '116'])).
% 1.12/1.34  thf('118', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.12/1.34      inference('cnf', [status(esa)], [t3_boole])).
% 1.12/1.34  thf('119', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.12/1.34      inference('demod', [status(thm)], ['112', '117', '118'])).
% 1.12/1.34  thf('120', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 1.12/1.34           = (X1))),
% 1.12/1.34      inference('demod', [status(thm)], ['84', '85'])).
% 1.12/1.34  thf('121', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 1.12/1.34           = (X0))),
% 1.12/1.34      inference('sup+', [status(thm)], ['119', '120'])).
% 1.12/1.34  thf('122', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.12/1.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.12/1.34  thf('123', plain,
% 1.12/1.34      (![X13 : $i, X14 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 1.12/1.34           = (k4_xboole_0 @ X13 @ X14))),
% 1.12/1.34      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.12/1.34  thf('124', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.12/1.34           = (k4_xboole_0 @ X0 @ X1))),
% 1.12/1.34      inference('sup+', [status(thm)], ['122', '123'])).
% 1.12/1.34  thf('125', plain,
% 1.12/1.34      (![X0 : $i, X1 : $i]:
% 1.12/1.34         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 1.12/1.34      inference('demod', [status(thm)], ['121', '124'])).
% 1.12/1.34  thf('126', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 1.12/1.34      inference('sup+', [status(thm)], ['107', '125'])).
% 1.12/1.34  thf('127', plain, (((sk_C) = (sk_B))),
% 1.12/1.34      inference('sup+', [status(thm)], ['59', '126'])).
% 1.12/1.34  thf('128', plain, (((sk_C) != (sk_B))),
% 1.12/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.34  thf('129', plain, ($false),
% 1.12/1.34      inference('simplify_reflect-', [status(thm)], ['127', '128'])).
% 1.12/1.34  
% 1.12/1.34  % SZS output end Refutation
% 1.12/1.34  
% 1.12/1.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
