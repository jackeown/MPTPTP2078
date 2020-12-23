%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L7a73moeF1

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:58 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 886 expanded)
%              Number of leaves         :   19 ( 306 expanded)
%              Depth                    :   21
%              Number of atoms          : 1142 (6995 expanded)
%              Number of equality atoms :  150 ( 916 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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

thf('0',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k4_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) )
    = sk_D ),
    inference('sup+',[status(thm)],['4','7'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_D )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['19','28'])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['8','11'])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k4_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('33',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_D @ sk_A ) @ k1_xboole_0 )
    = sk_D ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('39',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('41',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('45',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('48',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('51',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_D ) ) ),
    inference('sup+',[status(thm)],['43','55'])).

thf('57',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k4_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('58',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_D ) ) )
    = sk_A ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('64',plain,(
    sk_A = sk_D ),
    inference(demod,[status(thm)],['33','34','61','62','63'])).

thf('65',plain,(
    sk_A = sk_D ),
    inference(demod,[status(thm)],['33','34','61','62','63'])).

thf('66',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['12','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('68',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('69',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k4_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['67','73'])).

thf('75',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k4_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('78',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['66','81'])).

thf('83',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['12','64','65'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('88',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('90',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k4_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_D ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) )
      = ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) @ ( k3_xboole_0 @ sk_D @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) )
      = ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    sk_A = sk_D ),
    inference(demod,[status(thm)],['33','34','61','62','63'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) )
      = ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_B ) @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['88','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('101',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('104',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['98','99','102','103'])).

thf('105',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('106',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('109',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('110',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k4_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('111',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_A ) )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('113',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('116',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('118',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('120',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('122',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('125',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_A ) @ ( k4_xboole_0 @ sk_C_1 @ sk_B ) )
      = ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['113','127'])).

thf('129',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('130',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('131',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['111','112'])).

thf('132',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['132','135'])).

thf('137',plain,(
    sk_C_1 = sk_B ),
    inference(demod,[status(thm)],['106','107','108','136'])).

thf('138',plain,(
    sk_C_1 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['137','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L7a73moeF1
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.82/1.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.82/1.01  % Solved by: fo/fo7.sh
% 0.82/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.01  % done 1451 iterations in 0.555s
% 0.82/1.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.82/1.01  % SZS output start Refutation
% 0.82/1.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.82/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.82/1.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.82/1.01  thf(sk_D_type, type, sk_D: $i).
% 0.82/1.01  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.82/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.01  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.82/1.01  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.82/1.01  thf(t72_xboole_1, conjecture,
% 0.82/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.01     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.82/1.01         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.82/1.01       ( ( C ) = ( B ) ) ))).
% 0.82/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.01    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.01        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.82/1.01            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.82/1.01          ( ( C ) = ( B ) ) ) )),
% 0.82/1.01    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.82/1.01  thf('0', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf(d7_xboole_0, axiom,
% 0.82/1.01    (![A:$i,B:$i]:
% 0.82/1.01     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.82/1.01       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.82/1.01  thf('1', plain,
% 0.82/1.01      (![X4 : $i, X5 : $i]:
% 0.82/1.01         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.82/1.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.82/1.01  thf('2', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['0', '1'])).
% 0.82/1.01  thf(commutativity_k3_xboole_0, axiom,
% 0.82/1.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.82/1.01  thf('3', plain,
% 0.82/1.01      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.82/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.01  thf('4', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.82/1.01      inference('demod', [status(thm)], ['2', '3'])).
% 0.82/1.01  thf('5', plain,
% 0.82/1.01      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.82/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.01  thf(t51_xboole_1, axiom,
% 0.82/1.01    (![A:$i,B:$i]:
% 0.82/1.01     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.82/1.01       ( A ) ))).
% 0.82/1.01  thf('6', plain,
% 0.82/1.01      (![X23 : $i, X24 : $i]:
% 0.82/1.01         ((k2_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ (k4_xboole_0 @ X23 @ X24))
% 0.82/1.01           = (X23))),
% 0.82/1.01      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.82/1.01  thf('7', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.82/1.01           = (X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['5', '6'])).
% 0.82/1.01  thf('8', plain,
% 0.82/1.01      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B)) = (sk_D))),
% 0.82/1.01      inference('sup+', [status(thm)], ['4', '7'])).
% 0.82/1.01  thf(commutativity_k2_xboole_0, axiom,
% 0.82/1.01    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.82/1.01  thf('9', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.82/1.01      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.82/1.01  thf(t1_boole, axiom,
% 0.82/1.01    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.82/1.01  thf('10', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.82/1.01      inference('cnf', [status(esa)], [t1_boole])).
% 0.82/1.01  thf('11', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['9', '10'])).
% 0.82/1.01  thf('12', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 0.82/1.01      inference('demod', [status(thm)], ['8', '11'])).
% 0.82/1.01  thf('13', plain,
% 0.82/1.01      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('14', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.82/1.01      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.82/1.01  thf('15', plain,
% 0.82/1.01      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.82/1.01      inference('demod', [status(thm)], ['13', '14'])).
% 0.82/1.01  thf(t41_xboole_1, axiom,
% 0.82/1.01    (![A:$i,B:$i,C:$i]:
% 0.82/1.01     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.82/1.01       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.82/1.01  thf('16', plain,
% 0.82/1.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.82/1.01           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.82/1.01      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.82/1.01  thf('17', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_D)
% 0.82/1.01           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.82/1.01      inference('sup+', [status(thm)], ['15', '16'])).
% 0.82/1.01  thf('18', plain,
% 0.82/1.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.82/1.01           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.82/1.01      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.82/1.01  thf('19', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_D)
% 0.82/1.01           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.82/1.01      inference('demod', [status(thm)], ['17', '18'])).
% 0.82/1.01  thf(t39_xboole_1, axiom,
% 0.82/1.01    (![A:$i,B:$i]:
% 0.82/1.01     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.82/1.01  thf('20', plain,
% 0.82/1.01      (![X13 : $i, X14 : $i]:
% 0.82/1.01         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.82/1.01           = (k2_xboole_0 @ X13 @ X14))),
% 0.82/1.01      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.82/1.01  thf('21', plain,
% 0.82/1.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.82/1.01           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.82/1.01      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.82/1.01  thf('22', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 0.82/1.01           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.82/1.01      inference('sup+', [status(thm)], ['20', '21'])).
% 0.82/1.01  thf('23', plain,
% 0.82/1.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.82/1.01           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.82/1.01      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.82/1.01  thf('24', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 0.82/1.01           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.82/1.01      inference('demod', [status(thm)], ['22', '23'])).
% 0.82/1.01  thf('25', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.82/1.01      inference('cnf', [status(esa)], [t1_boole])).
% 0.82/1.01  thf(t46_xboole_1, axiom,
% 0.82/1.01    (![A:$i,B:$i]:
% 0.82/1.01     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.82/1.01  thf('26', plain,
% 0.82/1.01      (![X19 : $i, X20 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 0.82/1.01      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.82/1.01  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['25', '26'])).
% 0.82/1.01  thf('28', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['24', '27'])).
% 0.82/1.01  thf('29', plain,
% 0.82/1.01      (((k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A) = (k1_xboole_0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['19', '28'])).
% 0.82/1.01  thf('30', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 0.82/1.01      inference('demod', [status(thm)], ['8', '11'])).
% 0.82/1.01  thf('31', plain, (((k4_xboole_0 @ sk_D @ sk_A) = (k1_xboole_0))),
% 0.82/1.01      inference('demod', [status(thm)], ['29', '30'])).
% 0.82/1.01  thf('32', plain,
% 0.82/1.01      (![X23 : $i, X24 : $i]:
% 0.82/1.01         ((k2_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ (k4_xboole_0 @ X23 @ X24))
% 0.82/1.01           = (X23))),
% 0.82/1.01      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.82/1.01  thf('33', plain,
% 0.82/1.01      (((k2_xboole_0 @ (k3_xboole_0 @ sk_D @ sk_A) @ k1_xboole_0) = (sk_D))),
% 0.82/1.01      inference('sup+', [status(thm)], ['31', '32'])).
% 0.82/1.01  thf('34', plain,
% 0.82/1.01      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.82/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.01  thf('35', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('36', plain,
% 0.82/1.01      (![X4 : $i, X5 : $i]:
% 0.82/1.01         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.82/1.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.82/1.01  thf('37', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['35', '36'])).
% 0.82/1.01  thf('38', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.82/1.01           = (X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['5', '6'])).
% 0.82/1.01  thf('39', plain,
% 0.82/1.01      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_1)) = (sk_A))),
% 0.82/1.01      inference('sup+', [status(thm)], ['37', '38'])).
% 0.82/1.01  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['9', '10'])).
% 0.82/1.01  thf('41', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (sk_A))),
% 0.82/1.01      inference('demod', [status(thm)], ['39', '40'])).
% 0.82/1.01  thf('42', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_D)
% 0.82/1.01           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.82/1.01      inference('demod', [status(thm)], ['17', '18'])).
% 0.82/1.01  thf('43', plain,
% 0.82/1.01      (((k4_xboole_0 @ sk_A @ sk_D)
% 0.82/1.01         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 0.82/1.01      inference('sup+', [status(thm)], ['41', '42'])).
% 0.82/1.01  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['25', '26'])).
% 0.82/1.01  thf('45', plain,
% 0.82/1.01      (![X13 : $i, X14 : $i]:
% 0.82/1.01         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.82/1.01           = (k2_xboole_0 @ X13 @ X14))),
% 0.82/1.01      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.82/1.01  thf('46', plain,
% 0.82/1.01      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['44', '45'])).
% 0.82/1.01  thf('47', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.82/1.01      inference('cnf', [status(esa)], [t1_boole])).
% 0.82/1.01  thf('48', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.82/1.01      inference('demod', [status(thm)], ['46', '47'])).
% 0.82/1.01  thf('49', plain,
% 0.82/1.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.82/1.01           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.82/1.01      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.82/1.01  thf('50', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.82/1.01           = (k4_xboole_0 @ X1 @ X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['48', '49'])).
% 0.82/1.01  thf(t48_xboole_1, axiom,
% 0.82/1.01    (![A:$i,B:$i]:
% 0.82/1.01     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.82/1.01  thf('51', plain,
% 0.82/1.01      (![X21 : $i, X22 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.82/1.01           = (k3_xboole_0 @ X21 @ X22))),
% 0.82/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.82/1.01  thf('52', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.82/1.01           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['50', '51'])).
% 0.82/1.01  thf('53', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['25', '26'])).
% 0.82/1.01  thf('54', plain,
% 0.82/1.01      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.82/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.01  thf('55', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.82/1.01      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.82/1.01  thf('56', plain,
% 0.82/1.01      (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_D)))),
% 0.82/1.01      inference('sup+', [status(thm)], ['43', '55'])).
% 0.82/1.01  thf('57', plain,
% 0.82/1.01      (![X23 : $i, X24 : $i]:
% 0.82/1.01         ((k2_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ (k4_xboole_0 @ X23 @ X24))
% 0.82/1.01           = (X23))),
% 0.82/1.01      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.82/1.01  thf('58', plain,
% 0.82/1.01      (((k2_xboole_0 @ k1_xboole_0 @ 
% 0.82/1.01         (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_D))) = (sk_A))),
% 0.82/1.01      inference('sup+', [status(thm)], ['56', '57'])).
% 0.82/1.01  thf('59', plain,
% 0.82/1.01      (![X21 : $i, X22 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.82/1.01           = (k3_xboole_0 @ X21 @ X22))),
% 0.82/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.82/1.01  thf('60', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['9', '10'])).
% 0.82/1.01  thf('61', plain, (((k3_xboole_0 @ sk_A @ sk_D) = (sk_A))),
% 0.82/1.01      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.82/1.01  thf('62', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.82/1.01      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.82/1.01  thf('63', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['9', '10'])).
% 0.82/1.01  thf('64', plain, (((sk_A) = (sk_D))),
% 0.82/1.01      inference('demod', [status(thm)], ['33', '34', '61', '62', '63'])).
% 0.82/1.01  thf('65', plain, (((sk_A) = (sk_D))),
% 0.82/1.01      inference('demod', [status(thm)], ['33', '34', '61', '62', '63'])).
% 0.82/1.01  thf('66', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.82/1.01      inference('demod', [status(thm)], ['12', '64', '65'])).
% 0.82/1.01  thf('67', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.82/1.01      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.82/1.01  thf('68', plain,
% 0.82/1.01      (![X19 : $i, X20 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 0.82/1.01      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.82/1.01  thf('69', plain,
% 0.82/1.01      (![X23 : $i, X24 : $i]:
% 0.82/1.01         ((k2_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ (k4_xboole_0 @ X23 @ X24))
% 0.82/1.01           = (X23))),
% 0.82/1.01      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.82/1.01  thf('70', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ 
% 0.82/1.01           k1_xboole_0) = (X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['68', '69'])).
% 0.82/1.01  thf('71', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.82/1.01      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.82/1.01  thf('72', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['9', '10'])).
% 0.82/1.01  thf('73', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 0.82/1.01      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.82/1.01  thf('74', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['67', '73'])).
% 0.82/1.01  thf('75', plain,
% 0.82/1.01      (![X23 : $i, X24 : $i]:
% 0.82/1.01         ((k2_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ (k4_xboole_0 @ X23 @ X24))
% 0.82/1.01           = (X23))),
% 0.82/1.01      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.82/1.01  thf('76', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 0.82/1.01           = (X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['74', '75'])).
% 0.82/1.01  thf('77', plain,
% 0.82/1.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.82/1.01           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.82/1.01      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.82/1.01  thf('78', plain,
% 0.82/1.01      (![X13 : $i, X14 : $i]:
% 0.82/1.01         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.82/1.01           = (k2_xboole_0 @ X13 @ X14))),
% 0.82/1.01      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.82/1.01  thf('79', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.82/1.01      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.82/1.01  thf('80', plain,
% 0.82/1.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.82/1.01           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.82/1.01      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.82/1.01  thf('81', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.82/1.01           = (k4_xboole_0 @ X2 @ X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['79', '80'])).
% 0.82/1.01  thf('82', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.82/1.01           = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.82/1.01      inference('sup+', [status(thm)], ['66', '81'])).
% 0.82/1.01  thf('83', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.82/1.01      inference('demod', [status(thm)], ['12', '64', '65'])).
% 0.82/1.01  thf('84', plain,
% 0.82/1.01      (![X0 : $i]: ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) = (sk_A))),
% 0.82/1.01      inference('demod', [status(thm)], ['82', '83'])).
% 0.82/1.01  thf('85', plain,
% 0.82/1.01      (![X21 : $i, X22 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.82/1.02           = (k3_xboole_0 @ X21 @ X22))),
% 0.82/1.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.82/1.02  thf('86', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((k4_xboole_0 @ sk_A @ sk_A)
% 0.82/1.02           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.82/1.02      inference('sup+', [status(thm)], ['84', '85'])).
% 0.82/1.02  thf('87', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.82/1.02      inference('sup+', [status(thm)], ['25', '26'])).
% 0.82/1.02  thf('88', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((k1_xboole_0) = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.82/1.02      inference('demod', [status(thm)], ['86', '87'])).
% 0.82/1.02  thf('89', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_D)
% 0.82/1.02           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.82/1.02      inference('demod', [status(thm)], ['17', '18'])).
% 0.82/1.02  thf('90', plain,
% 0.82/1.02      (![X23 : $i, X24 : $i]:
% 0.82/1.02         ((k2_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ (k4_xboole_0 @ X23 @ X24))
% 0.82/1.02           = (X23))),
% 0.82/1.02      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.82/1.02  thf('91', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((k2_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_D) @ 
% 0.82/1.02           (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))
% 0.82/1.02           = (k4_xboole_0 @ X0 @ sk_C_1))),
% 0.82/1.02      inference('sup+', [status(thm)], ['89', '90'])).
% 0.82/1.02  thf('92', plain,
% 0.82/1.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.82/1.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.02  thf('93', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.82/1.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.82/1.02  thf('94', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((k2_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A) @ 
% 0.82/1.02           (k3_xboole_0 @ sk_D @ (k4_xboole_0 @ X0 @ sk_C_1)))
% 0.82/1.02           = (k4_xboole_0 @ X0 @ sk_C_1))),
% 0.82/1.02      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.82/1.02  thf('95', plain, (((sk_A) = (sk_D))),
% 0.82/1.02      inference('demod', [status(thm)], ['33', '34', '61', '62', '63'])).
% 0.82/1.02  thf('96', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.82/1.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.82/1.02  thf('97', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1)) @ 
% 0.82/1.02           (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))
% 0.82/1.02           = (k4_xboole_0 @ X0 @ sk_C_1))),
% 0.82/1.02      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.82/1.02  thf('98', plain,
% 0.82/1.02      (((k2_xboole_0 @ k1_xboole_0 @ 
% 0.82/1.02         (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_B) @ sk_A))
% 0.82/1.02         = (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.82/1.02      inference('sup+', [status(thm)], ['88', '97'])).
% 0.82/1.02  thf('99', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.82/1.02      inference('sup+', [status(thm)], ['25', '26'])).
% 0.82/1.02  thf('100', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.82/1.02      inference('sup+', [status(thm)], ['9', '10'])).
% 0.82/1.02  thf('101', plain,
% 0.82/1.02      (![X19 : $i, X20 : $i]:
% 0.82/1.02         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 0.82/1.02      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.82/1.02  thf('102', plain,
% 0.82/1.02      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.82/1.02      inference('sup+', [status(thm)], ['100', '101'])).
% 0.82/1.02  thf('103', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.82/1.02      inference('sup+', [status(thm)], ['9', '10'])).
% 0.82/1.02  thf('104', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.82/1.02      inference('demod', [status(thm)], ['98', '99', '102', '103'])).
% 0.82/1.02  thf('105', plain,
% 0.82/1.02      (![X13 : $i, X14 : $i]:
% 0.82/1.02         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.82/1.02           = (k2_xboole_0 @ X13 @ X14))),
% 0.82/1.02      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.82/1.02  thf('106', plain,
% 0.82/1.02      (((k2_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k2_xboole_0 @ sk_C_1 @ sk_B))),
% 0.82/1.02      inference('sup+', [status(thm)], ['104', '105'])).
% 0.82/1.02  thf('107', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.82/1.02      inference('cnf', [status(esa)], [t1_boole])).
% 0.82/1.02  thf('108', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.82/1.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.82/1.02  thf('109', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.82/1.02      inference('sup-', [status(thm)], ['35', '36'])).
% 0.82/1.02  thf('110', plain,
% 0.82/1.02      (![X23 : $i, X24 : $i]:
% 0.82/1.02         ((k2_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ (k4_xboole_0 @ X23 @ X24))
% 0.82/1.02           = (X23))),
% 0.82/1.02      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.82/1.02  thf('111', plain,
% 0.82/1.02      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_A)) = (sk_C_1))),
% 0.82/1.02      inference('sup+', [status(thm)], ['109', '110'])).
% 0.82/1.02  thf('112', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.82/1.02      inference('sup+', [status(thm)], ['9', '10'])).
% 0.82/1.02  thf('113', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.82/1.02      inference('demod', [status(thm)], ['111', '112'])).
% 0.82/1.02  thf('114', plain,
% 0.82/1.02      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('115', plain,
% 0.82/1.02      (![X19 : $i, X20 : $i]:
% 0.82/1.02         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 0.82/1.02      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.82/1.02  thf('116', plain,
% 0.82/1.02      (((k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.82/1.02      inference('sup+', [status(thm)], ['114', '115'])).
% 0.82/1.02  thf('117', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.82/1.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.82/1.02  thf('118', plain,
% 0.82/1.02      (((k4_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 0.82/1.02      inference('demod', [status(thm)], ['116', '117'])).
% 0.82/1.02  thf('119', plain,
% 0.82/1.02      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.82/1.02         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.82/1.02           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.82/1.02      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.82/1.02  thf('120', plain,
% 0.82/1.02      (((k4_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_B) @ sk_A) = (k1_xboole_0))),
% 0.82/1.02      inference('demod', [status(thm)], ['118', '119'])).
% 0.82/1.02  thf('121', plain,
% 0.82/1.02      (![X13 : $i, X14 : $i]:
% 0.82/1.02         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.82/1.02           = (k2_xboole_0 @ X13 @ X14))),
% 0.82/1.02      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.82/1.02  thf('122', plain,
% 0.82/1.02      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 0.82/1.02         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.82/1.02      inference('sup+', [status(thm)], ['120', '121'])).
% 0.82/1.02  thf('123', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.82/1.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.82/1.02  thf('124', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.82/1.02      inference('sup+', [status(thm)], ['9', '10'])).
% 0.82/1.02  thf('125', plain,
% 0.82/1.02      (((sk_A) = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.82/1.02      inference('demod', [status(thm)], ['122', '123', '124'])).
% 0.82/1.02  thf('126', plain,
% 0.82/1.02      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.82/1.02         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.82/1.02           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.82/1.02      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.82/1.02  thf('127', plain,
% 0.82/1.02      (![X0 : $i]:
% 0.82/1.02         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_A) @ 
% 0.82/1.02           (k4_xboole_0 @ sk_C_1 @ sk_B)) = (k4_xboole_0 @ X0 @ sk_A))),
% 0.82/1.02      inference('sup+', [status(thm)], ['125', '126'])).
% 0.82/1.02  thf('128', plain,
% 0.82/1.02      (((k4_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_C_1 @ sk_B))
% 0.82/1.02         = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 0.82/1.02      inference('sup+', [status(thm)], ['113', '127'])).
% 0.82/1.02  thf('129', plain,
% 0.82/1.02      (![X21 : $i, X22 : $i]:
% 0.82/1.02         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.82/1.02           = (k3_xboole_0 @ X21 @ X22))),
% 0.82/1.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.82/1.02  thf('130', plain,
% 0.82/1.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.82/1.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.02  thf('131', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.82/1.02      inference('demod', [status(thm)], ['111', '112'])).
% 0.82/1.02  thf('132', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (sk_C_1))),
% 0.82/1.02      inference('demod', [status(thm)], ['128', '129', '130', '131'])).
% 0.82/1.02  thf('133', plain,
% 0.82/1.02      (![X21 : $i, X22 : $i]:
% 0.82/1.02         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.82/1.02           = (k3_xboole_0 @ X21 @ X22))),
% 0.82/1.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.82/1.02  thf('134', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i]:
% 0.82/1.02         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.82/1.02      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.82/1.02  thf('135', plain,
% 0.82/1.02      (![X0 : $i, X1 : $i]:
% 0.82/1.02         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 0.82/1.02      inference('sup+', [status(thm)], ['133', '134'])).
% 0.82/1.02  thf('136', plain, (((k2_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 0.82/1.02      inference('sup+', [status(thm)], ['132', '135'])).
% 0.82/1.02  thf('137', plain, (((sk_C_1) = (sk_B))),
% 0.82/1.02      inference('demod', [status(thm)], ['106', '107', '108', '136'])).
% 0.82/1.02  thf('138', plain, (((sk_C_1) != (sk_B))),
% 0.82/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.02  thf('139', plain, ($false),
% 0.82/1.02      inference('simplify_reflect-', [status(thm)], ['137', '138'])).
% 0.82/1.02  
% 0.82/1.02  % SZS output end Refutation
% 0.82/1.02  
% 0.82/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
