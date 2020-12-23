%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RjeqcDEuya

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:01 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 827 expanded)
%              Number of leaves         :   21 ( 281 expanded)
%              Depth                    :   19
%              Number of atoms          : 1112 (6130 expanded)
%              Number of equality atoms :  143 ( 819 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf('3',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('21',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('29',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) )
    = sk_D ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('31',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['11','24','35'])).

thf('37',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('38',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('40',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('44',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_A ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('53',plain,
    ( ( k2_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('56',plain,
    ( sk_D
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['36','56'])).

thf('58',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['2','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('61',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','73'])).

thf('75',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('77',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('79',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('81',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = sk_B ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('83',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_D @ X0 ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['74','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['36','56'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['58','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('94',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('96',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('97',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('99',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('101',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('103',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['101','106'])).

thf('108',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('123',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['107','130'])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('132',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9 = X8 )
      | ( ( k4_xboole_0 @ X9 @ X8 )
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('133',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_C )
     != k1_xboole_0 )
    | ( sk_B = sk_C ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['133','134'])).

thf('136',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['94','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RjeqcDEuya
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.15/1.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.15/1.34  % Solved by: fo/fo7.sh
% 1.15/1.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.34  % done 2022 iterations in 0.881s
% 1.15/1.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.15/1.34  % SZS output start Refutation
% 1.15/1.34  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.15/1.34  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.34  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.15/1.34  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.15/1.34  thf(sk_B_type, type, sk_B: $i).
% 1.15/1.34  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.15/1.34  thf(sk_D_type, type, sk_D: $i).
% 1.15/1.34  thf(sk_C_type, type, sk_C: $i).
% 1.15/1.34  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.15/1.34  thf(t72_xboole_1, conjecture,
% 1.15/1.34    (![A:$i,B:$i,C:$i,D:$i]:
% 1.15/1.34     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 1.15/1.34         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 1.15/1.34       ( ( C ) = ( B ) ) ))).
% 1.15/1.34  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.34    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.15/1.34        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 1.15/1.34            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 1.15/1.34          ( ( C ) = ( B ) ) ) )),
% 1.15/1.34    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 1.15/1.34  thf('0', plain,
% 1.15/1.34      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf(commutativity_k2_xboole_0, axiom,
% 1.15/1.34    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.15/1.34  thf('1', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.15/1.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.15/1.34  thf('2', plain,
% 1.15/1.34      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.15/1.34      inference('demod', [status(thm)], ['0', '1'])).
% 1.15/1.34  thf('3', plain,
% 1.15/1.34      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.15/1.34      inference('demod', [status(thm)], ['0', '1'])).
% 1.15/1.34  thf('4', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.15/1.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.15/1.34  thf(t46_xboole_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.15/1.34  thf('5', plain,
% 1.15/1.34      (![X16 : $i, X17 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17)) = (k1_xboole_0))),
% 1.15/1.34      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.15/1.34  thf('6', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.15/1.34      inference('sup+', [status(thm)], ['4', '5'])).
% 1.15/1.34  thf('7', plain,
% 1.15/1.34      (((k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 1.15/1.34      inference('sup+', [status(thm)], ['3', '6'])).
% 1.15/1.34  thf(t41_xboole_1, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.15/1.34       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.15/1.34  thf('8', plain,
% 1.15/1.34      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.15/1.34           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.15/1.34      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.15/1.34  thf(t39_xboole_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.15/1.34  thf('9', plain,
% 1.15/1.34      (![X10 : $i, X11 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.15/1.34           = (k2_xboole_0 @ X10 @ X11))),
% 1.15/1.34      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.15/1.34  thf('10', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.15/1.34           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 1.15/1.34      inference('sup+', [status(thm)], ['8', '9'])).
% 1.15/1.34  thf('11', plain,
% 1.15/1.34      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 1.15/1.34         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B)))),
% 1.15/1.34      inference('sup+', [status(thm)], ['7', '10'])).
% 1.15/1.34  thf(t3_boole, axiom,
% 1.15/1.34    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.15/1.34  thf('12', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.15/1.34      inference('cnf', [status(esa)], [t3_boole])).
% 1.15/1.34  thf(t48_xboole_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.15/1.34  thf('13', plain,
% 1.15/1.34      (![X18 : $i, X19 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.15/1.34           = (k3_xboole_0 @ X18 @ X19))),
% 1.15/1.34      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.34  thf('14', plain,
% 1.15/1.34      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.15/1.34      inference('sup+', [status(thm)], ['12', '13'])).
% 1.15/1.34  thf(t2_boole, axiom,
% 1.15/1.34    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.15/1.34  thf('15', plain,
% 1.15/1.34      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 1.15/1.34      inference('cnf', [status(esa)], [t2_boole])).
% 1.15/1.34  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.15/1.34      inference('demod', [status(thm)], ['14', '15'])).
% 1.15/1.34  thf('17', plain,
% 1.15/1.34      (![X18 : $i, X19 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.15/1.34           = (k3_xboole_0 @ X18 @ X19))),
% 1.15/1.34      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.34  thf('18', plain,
% 1.15/1.34      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.15/1.34      inference('sup+', [status(thm)], ['16', '17'])).
% 1.15/1.34  thf('19', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.15/1.34      inference('cnf', [status(esa)], [t3_boole])).
% 1.15/1.34  thf('20', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.15/1.34      inference('demod', [status(thm)], ['18', '19'])).
% 1.15/1.34  thf(t51_xboole_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.15/1.34       ( A ) ))).
% 1.15/1.34  thf('21', plain,
% 1.15/1.34      (![X20 : $i, X21 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 1.15/1.34           = (X20))),
% 1.15/1.34      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.15/1.34  thf('22', plain,
% 1.15/1.34      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 1.15/1.34      inference('sup+', [status(thm)], ['20', '21'])).
% 1.15/1.34  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.15/1.34      inference('demod', [status(thm)], ['14', '15'])).
% 1.15/1.34  thf('24', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.15/1.34      inference('demod', [status(thm)], ['22', '23'])).
% 1.15/1.34  thf('25', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf(d7_xboole_0, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.15/1.34       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.15/1.34  thf('26', plain,
% 1.15/1.34      (![X2 : $i, X3 : $i]:
% 1.15/1.34         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.15/1.34      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.15/1.34  thf('27', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['25', '26'])).
% 1.15/1.34  thf('28', plain,
% 1.15/1.34      (![X20 : $i, X21 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 1.15/1.34           = (X20))),
% 1.15/1.34      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.15/1.34  thf('29', plain,
% 1.15/1.34      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B)) = (sk_D))),
% 1.15/1.34      inference('sup+', [status(thm)], ['27', '28'])).
% 1.15/1.34  thf('30', plain,
% 1.15/1.34      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 1.15/1.34      inference('cnf', [status(esa)], [t2_boole])).
% 1.15/1.34  thf('31', plain,
% 1.15/1.34      (![X20 : $i, X21 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 1.15/1.34           = (X20))),
% 1.15/1.34      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.15/1.34  thf('32', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 1.15/1.34      inference('sup+', [status(thm)], ['30', '31'])).
% 1.15/1.34  thf('33', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.15/1.34      inference('cnf', [status(esa)], [t3_boole])).
% 1.15/1.34  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.15/1.34      inference('demod', [status(thm)], ['32', '33'])).
% 1.15/1.34  thf('35', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 1.15/1.34      inference('demod', [status(thm)], ['29', '34'])).
% 1.15/1.34  thf('36', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 1.15/1.34      inference('demod', [status(thm)], ['11', '24', '35'])).
% 1.15/1.34  thf('37', plain,
% 1.15/1.34      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.15/1.34      inference('demod', [status(thm)], ['0', '1'])).
% 1.15/1.34  thf('38', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf(symmetry_r1_xboole_0, axiom,
% 1.15/1.34    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.15/1.34  thf('39', plain,
% 1.15/1.34      (![X5 : $i, X6 : $i]:
% 1.15/1.34         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 1.15/1.34      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.15/1.34  thf('40', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 1.15/1.34      inference('sup-', [status(thm)], ['38', '39'])).
% 1.15/1.34  thf('41', plain,
% 1.15/1.34      (![X2 : $i, X3 : $i]:
% 1.15/1.34         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.15/1.34      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.15/1.34  thf('42', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['40', '41'])).
% 1.15/1.34  thf('43', plain,
% 1.15/1.34      (![X20 : $i, X21 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 1.15/1.34           = (X20))),
% 1.15/1.34      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.15/1.34  thf('44', plain,
% 1.15/1.34      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_A))),
% 1.15/1.34      inference('sup+', [status(thm)], ['42', '43'])).
% 1.15/1.34  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.15/1.34      inference('demod', [status(thm)], ['32', '33'])).
% 1.15/1.34  thf('46', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 1.15/1.34      inference('demod', [status(thm)], ['44', '45'])).
% 1.15/1.34  thf('47', plain,
% 1.15/1.34      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.15/1.34           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.15/1.34      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.15/1.34  thf('48', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ sk_A @ X0)
% 1.15/1.34           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0)))),
% 1.15/1.34      inference('sup+', [status(thm)], ['46', '47'])).
% 1.15/1.34  thf('49', plain,
% 1.15/1.34      (((k4_xboole_0 @ sk_A @ sk_D)
% 1.15/1.34         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.15/1.34      inference('sup+', [status(thm)], ['37', '48'])).
% 1.15/1.34  thf('50', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.15/1.34      inference('sup+', [status(thm)], ['4', '5'])).
% 1.15/1.34  thf('51', plain, (((k4_xboole_0 @ sk_A @ sk_D) = (k1_xboole_0))),
% 1.15/1.34      inference('demod', [status(thm)], ['49', '50'])).
% 1.15/1.34  thf('52', plain,
% 1.15/1.34      (![X10 : $i, X11 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.15/1.34           = (k2_xboole_0 @ X10 @ X11))),
% 1.15/1.34      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.15/1.34  thf('53', plain,
% 1.15/1.34      (((k2_xboole_0 @ sk_D @ k1_xboole_0) = (k2_xboole_0 @ sk_D @ sk_A))),
% 1.15/1.34      inference('sup+', [status(thm)], ['51', '52'])).
% 1.15/1.34  thf('54', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.15/1.34      inference('demod', [status(thm)], ['22', '23'])).
% 1.15/1.34  thf('55', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.15/1.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.15/1.34  thf('56', plain, (((sk_D) = (k2_xboole_0 @ sk_A @ sk_D))),
% 1.15/1.34      inference('demod', [status(thm)], ['53', '54', '55'])).
% 1.15/1.34  thf('57', plain, (((sk_D) = (sk_A))),
% 1.15/1.34      inference('sup+', [status(thm)], ['36', '56'])).
% 1.15/1.34  thf('58', plain,
% 1.15/1.34      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_A))),
% 1.15/1.34      inference('demod', [status(thm)], ['2', '57'])).
% 1.15/1.34  thf('59', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.15/1.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.15/1.34  thf('60', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.15/1.34      inference('sup+', [status(thm)], ['4', '5'])).
% 1.15/1.34  thf('61', plain,
% 1.15/1.34      (![X10 : $i, X11 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.15/1.34           = (k2_xboole_0 @ X10 @ X11))),
% 1.15/1.34      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.15/1.34  thf('62', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 1.15/1.34           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 1.15/1.34      inference('sup+', [status(thm)], ['60', '61'])).
% 1.15/1.34  thf('63', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.15/1.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.15/1.34  thf('64', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.15/1.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.15/1.34  thf('65', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X1 @ X0))
% 1.15/1.34           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.15/1.34      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.15/1.34  thf('66', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X1 @ X0))
% 1.15/1.34           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.15/1.34      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.15/1.34  thf('67', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ k1_xboole_0 @ 
% 1.15/1.34           (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 1.15/1.34           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.15/1.34              (k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.15/1.34      inference('sup+', [status(thm)], ['65', '66'])).
% 1.15/1.34  thf('68', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X1 @ X0))
% 1.15/1.34           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.15/1.34      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.15/1.34  thf('69', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ k1_xboole_0 @ 
% 1.15/1.34           (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 1.15/1.34           = (k2_xboole_0 @ k1_xboole_0 @ 
% 1.15/1.34              (k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.15/1.34      inference('demod', [status(thm)], ['67', '68'])).
% 1.15/1.34  thf('70', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.15/1.34      inference('demod', [status(thm)], ['32', '33'])).
% 1.15/1.34  thf('71', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.15/1.34      inference('demod', [status(thm)], ['32', '33'])).
% 1.15/1.34  thf('72', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.15/1.34      inference('demod', [status(thm)], ['32', '33'])).
% 1.15/1.34  thf('73', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.15/1.34           = (k2_xboole_0 @ X1 @ X0))),
% 1.15/1.34      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 1.15/1.34  thf('74', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.15/1.34           = (k2_xboole_0 @ X0 @ X1))),
% 1.15/1.34      inference('sup+', [status(thm)], ['59', '73'])).
% 1.15/1.34  thf('75', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('76', plain,
% 1.15/1.34      (![X5 : $i, X6 : $i]:
% 1.15/1.34         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 1.15/1.34      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.15/1.34  thf('77', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 1.15/1.34      inference('sup-', [status(thm)], ['75', '76'])).
% 1.15/1.34  thf('78', plain,
% 1.15/1.34      (![X2 : $i, X3 : $i]:
% 1.15/1.34         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.15/1.34      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.15/1.34  thf('79', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['77', '78'])).
% 1.15/1.34  thf('80', plain,
% 1.15/1.34      (![X20 : $i, X21 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 1.15/1.34           = (X20))),
% 1.15/1.34      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.15/1.34  thf('81', plain,
% 1.15/1.34      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_D)) = (sk_B))),
% 1.15/1.34      inference('sup+', [status(thm)], ['79', '80'])).
% 1.15/1.34  thf('82', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.15/1.34      inference('demod', [status(thm)], ['32', '33'])).
% 1.15/1.34  thf('83', plain, (((k4_xboole_0 @ sk_B @ sk_D) = (sk_B))),
% 1.15/1.34      inference('demod', [status(thm)], ['81', '82'])).
% 1.15/1.34  thf('84', plain,
% 1.15/1.34      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.15/1.34           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.15/1.34      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.15/1.34  thf('85', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ sk_B @ X0)
% 1.15/1.34           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_D @ X0)))),
% 1.15/1.34      inference('sup+', [status(thm)], ['83', '84'])).
% 1.15/1.34  thf('86', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_D @ X0))
% 1.15/1.34           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_D)))),
% 1.15/1.34      inference('sup+', [status(thm)], ['74', '85'])).
% 1.15/1.34  thf('87', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ sk_B @ X0)
% 1.15/1.34           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_D @ X0)))),
% 1.15/1.34      inference('sup+', [status(thm)], ['83', '84'])).
% 1.15/1.34  thf('88', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ sk_B @ X0)
% 1.15/1.34           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_D)))),
% 1.15/1.34      inference('demod', [status(thm)], ['86', '87'])).
% 1.15/1.34  thf('89', plain, (((sk_D) = (sk_A))),
% 1.15/1.34      inference('sup+', [status(thm)], ['36', '56'])).
% 1.15/1.34  thf('90', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ sk_B @ X0)
% 1.15/1.34           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_A)))),
% 1.15/1.34      inference('demod', [status(thm)], ['88', '89'])).
% 1.15/1.34  thf('91', plain,
% 1.15/1.34      (((k4_xboole_0 @ sk_B @ sk_C)
% 1.15/1.34         = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.15/1.34      inference('sup+', [status(thm)], ['58', '90'])).
% 1.15/1.34  thf('92', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ sk_B @ X0)
% 1.15/1.34           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_A)))),
% 1.15/1.34      inference('demod', [status(thm)], ['88', '89'])).
% 1.15/1.34  thf('93', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.15/1.34      inference('demod', [status(thm)], ['14', '15'])).
% 1.15/1.34  thf('94', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 1.15/1.34      inference('demod', [status(thm)], ['91', '92', '93'])).
% 1.15/1.34  thf('95', plain,
% 1.15/1.34      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.15/1.34      inference('demod', [status(thm)], ['0', '1'])).
% 1.15/1.34  thf('96', plain,
% 1.15/1.34      (![X16 : $i, X17 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17)) = (k1_xboole_0))),
% 1.15/1.34      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.15/1.34  thf('97', plain,
% 1.15/1.34      (((k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 1.15/1.34      inference('sup+', [status(thm)], ['95', '96'])).
% 1.15/1.34  thf('98', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.15/1.34           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 1.15/1.34      inference('sup+', [status(thm)], ['8', '9'])).
% 1.15/1.34  thf('99', plain,
% 1.15/1.34      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 1.15/1.34         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B)))),
% 1.15/1.34      inference('sup+', [status(thm)], ['97', '98'])).
% 1.15/1.34  thf('100', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.15/1.34      inference('demod', [status(thm)], ['22', '23'])).
% 1.15/1.34  thf('101', plain,
% 1.15/1.34      (((sk_A) = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B)))),
% 1.15/1.34      inference('demod', [status(thm)], ['99', '100'])).
% 1.15/1.34  thf('102', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.15/1.34      inference('sup+', [status(thm)], ['4', '5'])).
% 1.15/1.34  thf('103', plain,
% 1.15/1.34      (![X18 : $i, X19 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.15/1.34           = (k3_xboole_0 @ X18 @ X19))),
% 1.15/1.34      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.34  thf('104', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 1.15/1.34           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.15/1.34      inference('sup+', [status(thm)], ['102', '103'])).
% 1.15/1.34  thf('105', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.15/1.34      inference('cnf', [status(esa)], [t3_boole])).
% 1.15/1.34  thf('106', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.15/1.34      inference('demod', [status(thm)], ['104', '105'])).
% 1.15/1.34  thf('107', plain,
% 1.15/1.34      (((k4_xboole_0 @ sk_C @ sk_B)
% 1.15/1.34         = (k3_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 1.15/1.34      inference('sup+', [status(thm)], ['101', '106'])).
% 1.15/1.34  thf('108', plain,
% 1.15/1.34      (![X20 : $i, X21 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 1.15/1.34           = (X20))),
% 1.15/1.34      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.15/1.34  thf('109', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X1 @ X0))
% 1.15/1.34           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.15/1.34      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.15/1.34  thf('110', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ k1_xboole_0 @ 
% 1.15/1.34           (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))
% 1.15/1.34           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.15/1.34      inference('sup+', [status(thm)], ['108', '109'])).
% 1.15/1.34  thf('111', plain,
% 1.15/1.34      (![X20 : $i, X21 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 1.15/1.34           = (X20))),
% 1.15/1.34      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.15/1.34  thf('112', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.15/1.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.15/1.34  thf('113', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 1.15/1.34           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.15/1.34      inference('demod', [status(thm)], ['110', '111', '112'])).
% 1.15/1.34  thf('114', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.15/1.34      inference('demod', [status(thm)], ['32', '33'])).
% 1.15/1.34  thf('115', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.15/1.34      inference('demod', [status(thm)], ['113', '114'])).
% 1.15/1.34  thf('116', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ sk_A @ X0)
% 1.15/1.34           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0)))),
% 1.15/1.34      inference('sup+', [status(thm)], ['46', '47'])).
% 1.15/1.34  thf('117', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ X0))
% 1.15/1.34           = (k4_xboole_0 @ sk_A @ sk_C))),
% 1.15/1.34      inference('sup+', [status(thm)], ['115', '116'])).
% 1.15/1.34  thf('118', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 1.15/1.34      inference('demod', [status(thm)], ['44', '45'])).
% 1.15/1.34  thf('119', plain,
% 1.15/1.34      (![X0 : $i]: ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ X0)) = (sk_A))),
% 1.15/1.34      inference('demod', [status(thm)], ['117', '118'])).
% 1.15/1.34  thf('120', plain,
% 1.15/1.34      (![X18 : $i, X19 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.15/1.34           = (k3_xboole_0 @ X18 @ X19))),
% 1.15/1.34      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.34  thf('121', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((k4_xboole_0 @ sk_A @ sk_A)
% 1.15/1.34           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ X0)))),
% 1.15/1.34      inference('sup+', [status(thm)], ['119', '120'])).
% 1.15/1.34  thf('122', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.15/1.34      inference('demod', [status(thm)], ['14', '15'])).
% 1.15/1.34  thf('123', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((k1_xboole_0) = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ X0)))),
% 1.15/1.34      inference('demod', [status(thm)], ['121', '122'])).
% 1.15/1.34  thf('124', plain,
% 1.15/1.34      (![X2 : $i, X4 : $i]:
% 1.15/1.34         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.15/1.34      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.15/1.34  thf('125', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         (((k1_xboole_0) != (k1_xboole_0))
% 1.15/1.34          | (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ X0)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['123', '124'])).
% 1.15/1.34  thf('126', plain,
% 1.15/1.34      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ X0))),
% 1.15/1.34      inference('simplify', [status(thm)], ['125'])).
% 1.15/1.34  thf('127', plain,
% 1.15/1.34      (![X5 : $i, X6 : $i]:
% 1.15/1.34         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 1.15/1.34      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.15/1.34  thf('128', plain,
% 1.15/1.34      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_C @ X0) @ sk_A)),
% 1.15/1.34      inference('sup-', [status(thm)], ['126', '127'])).
% 1.15/1.34  thf('129', plain,
% 1.15/1.34      (![X2 : $i, X3 : $i]:
% 1.15/1.34         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.15/1.34      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.15/1.34  thf('130', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((k3_xboole_0 @ (k4_xboole_0 @ sk_C @ X0) @ sk_A) = (k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['128', '129'])).
% 1.15/1.34  thf('131', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 1.15/1.34      inference('demod', [status(thm)], ['107', '130'])).
% 1.15/1.34  thf(t32_xboole_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 1.15/1.34       ( ( A ) = ( B ) ) ))).
% 1.15/1.34  thf('132', plain,
% 1.15/1.34      (![X8 : $i, X9 : $i]:
% 1.15/1.34         (((X9) = (X8)) | ((k4_xboole_0 @ X9 @ X8) != (k4_xboole_0 @ X8 @ X9)))),
% 1.15/1.34      inference('cnf', [status(esa)], [t32_xboole_1])).
% 1.15/1.34  thf('133', plain,
% 1.15/1.34      ((((k4_xboole_0 @ sk_B @ sk_C) != (k1_xboole_0)) | ((sk_B) = (sk_C)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['131', '132'])).
% 1.15/1.34  thf('134', plain, (((sk_C) != (sk_B))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('135', plain, (((k4_xboole_0 @ sk_B @ sk_C) != (k1_xboole_0))),
% 1.15/1.34      inference('simplify_reflect-', [status(thm)], ['133', '134'])).
% 1.15/1.34  thf('136', plain, ($false),
% 1.15/1.34      inference('simplify_reflect-', [status(thm)], ['94', '135'])).
% 1.15/1.34  
% 1.15/1.34  % SZS output end Refutation
% 1.15/1.34  
% 1.15/1.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
