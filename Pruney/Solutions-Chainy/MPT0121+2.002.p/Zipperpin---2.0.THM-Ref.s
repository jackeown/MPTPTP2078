%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XH3evrtyfQ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:51 EST 2020

% Result     : Theorem 5.38s
% Output     : Refutation 5.38s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 732 expanded)
%              Number of leaves         :   21 ( 250 expanded)
%              Depth                    :   26
%              Number of atoms          : 1482 (5445 expanded)
%              Number of equality atoms :  149 ( 654 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t114_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ D )
        & ( r1_xboole_0 @ B @ D )
        & ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_xboole_0 @ A @ D )
          & ( r1_xboole_0 @ B @ D )
          & ( r1_xboole_0 @ C @ D ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t114_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_C ) @ sk_D ) ),
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

thf('2',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('5',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

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
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('10',plain,(
    r1_xboole_0 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_A )
    = ( k5_xboole_0 @ sk_D @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_A )
    = sk_D ),
    inference(demod,[status(thm)],['14','19'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_D @ X0 )
      = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_D @ X0 ) )
      = ( k3_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_D @ X0 )
      = ( k3_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_D @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','28'])).

thf('30',plain,(
    r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('32',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('34',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('36',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_D )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('38',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_D )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('41',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('42',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('49',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','60'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('62',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','66'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('68',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('69',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','59'])).

thf('80',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['78','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['78','84'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['78','84'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('92',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['90','95'])).

thf('97',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('98',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('101',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['96','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['77','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('107',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('112',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','113'])).

thf('115',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('118',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('119',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['117','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['116','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','60'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','60'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105','128','129','130','131','132','133'])).

thf('135',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('144',plain,(
    r1_xboole_0 @ sk_D @ sk_C ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('146',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('148',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_C )
    = ( k5_xboole_0 @ sk_D @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('150',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_D @ X0 )
      = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_D @ X0 ) )
      = ( k3_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_D @ X0 )
      = ( k3_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_D @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ X0 @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['141','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['38','160'])).

thf('162',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('163',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ) @ sk_D ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    $false ),
    inference(demod,[status(thm)],['2','163'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XH3evrtyfQ
% 0.14/0.33  % Computer   : n010.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:33:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 5.38/5.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.38/5.55  % Solved by: fo/fo7.sh
% 5.38/5.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.38/5.55  % done 6537 iterations in 5.110s
% 5.38/5.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.38/5.55  % SZS output start Refutation
% 5.38/5.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.38/5.55  thf(sk_C_type, type, sk_C: $i).
% 5.38/5.55  thf(sk_A_type, type, sk_A: $i).
% 5.38/5.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.38/5.55  thf(sk_D_type, type, sk_D: $i).
% 5.38/5.55  thf(sk_B_type, type, sk_B: $i).
% 5.38/5.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.38/5.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.38/5.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.38/5.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.38/5.55  thf(t114_xboole_1, conjecture,
% 5.38/5.55    (![A:$i,B:$i,C:$i,D:$i]:
% 5.38/5.55     ( ( ( r1_xboole_0 @ A @ D ) & ( r1_xboole_0 @ B @ D ) & 
% 5.38/5.55         ( r1_xboole_0 @ C @ D ) ) =>
% 5.38/5.55       ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ))).
% 5.38/5.55  thf(zf_stmt_0, negated_conjecture,
% 5.38/5.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 5.38/5.55        ( ( ( r1_xboole_0 @ A @ D ) & ( r1_xboole_0 @ B @ D ) & 
% 5.38/5.55            ( r1_xboole_0 @ C @ D ) ) =>
% 5.38/5.55          ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) )),
% 5.38/5.55    inference('cnf.neg', [status(esa)], [t114_xboole_1])).
% 5.38/5.55  thf('0', plain,
% 5.38/5.55      (~ (r1_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_C) @ 
% 5.38/5.55          sk_D)),
% 5.38/5.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.38/5.55  thf(commutativity_k2_xboole_0, axiom,
% 5.38/5.55    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 5.38/5.55  thf('1', plain,
% 5.38/5.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.38/5.55      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.38/5.55  thf('2', plain,
% 5.38/5.55      (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B)) @ 
% 5.38/5.55          sk_D)),
% 5.38/5.55      inference('demod', [status(thm)], ['0', '1'])).
% 5.38/5.55  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 5.38/5.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.38/5.55  thf(symmetry_r1_xboole_0, axiom,
% 5.38/5.55    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 5.38/5.55  thf('4', plain,
% 5.38/5.55      (![X5 : $i, X6 : $i]:
% 5.38/5.55         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 5.38/5.55      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.38/5.55  thf('5', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 5.38/5.55      inference('sup-', [status(thm)], ['3', '4'])).
% 5.38/5.55  thf(d7_xboole_0, axiom,
% 5.38/5.55    (![A:$i,B:$i]:
% 5.38/5.55     ( ( r1_xboole_0 @ A @ B ) <=>
% 5.38/5.55       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 5.38/5.55  thf('6', plain,
% 5.38/5.55      (![X2 : $i, X3 : $i]:
% 5.38/5.55         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 5.38/5.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.38/5.55  thf('7', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 5.38/5.55      inference('sup-', [status(thm)], ['5', '6'])).
% 5.38/5.55  thf('8', plain, ((r1_xboole_0 @ sk_A @ sk_D)),
% 5.38/5.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.38/5.55  thf('9', plain,
% 5.38/5.55      (![X5 : $i, X6 : $i]:
% 5.38/5.55         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 5.38/5.55      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.38/5.55  thf('10', plain, ((r1_xboole_0 @ sk_D @ sk_A)),
% 5.38/5.55      inference('sup-', [status(thm)], ['8', '9'])).
% 5.38/5.55  thf('11', plain,
% 5.38/5.55      (![X2 : $i, X3 : $i]:
% 5.38/5.55         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 5.38/5.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.38/5.55  thf('12', plain, (((k3_xboole_0 @ sk_D @ sk_A) = (k1_xboole_0))),
% 5.38/5.55      inference('sup-', [status(thm)], ['10', '11'])).
% 5.38/5.55  thf(t100_xboole_1, axiom,
% 5.38/5.55    (![A:$i,B:$i]:
% 5.38/5.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.38/5.55  thf('13', plain,
% 5.38/5.55      (![X7 : $i, X8 : $i]:
% 5.38/5.55         ((k4_xboole_0 @ X7 @ X8)
% 5.38/5.55           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 5.38/5.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.38/5.55  thf('14', plain,
% 5.38/5.55      (((k4_xboole_0 @ sk_D @ sk_A) = (k5_xboole_0 @ sk_D @ k1_xboole_0))),
% 5.38/5.55      inference('sup+', [status(thm)], ['12', '13'])).
% 5.38/5.55  thf(t2_boole, axiom,
% 5.38/5.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 5.38/5.55  thf('15', plain,
% 5.38/5.55      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 5.38/5.55      inference('cnf', [status(esa)], [t2_boole])).
% 5.38/5.55  thf('16', plain,
% 5.38/5.55      (![X7 : $i, X8 : $i]:
% 5.38/5.55         ((k4_xboole_0 @ X7 @ X8)
% 5.38/5.55           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 5.38/5.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.38/5.55  thf('17', plain,
% 5.38/5.55      (![X0 : $i]:
% 5.38/5.55         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.38/5.55      inference('sup+', [status(thm)], ['15', '16'])).
% 5.38/5.55  thf(t3_boole, axiom,
% 5.38/5.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.38/5.55  thf('18', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 5.38/5.55      inference('cnf', [status(esa)], [t3_boole])).
% 5.38/5.55  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.38/5.55      inference('sup+', [status(thm)], ['17', '18'])).
% 5.38/5.55  thf('20', plain, (((k4_xboole_0 @ sk_D @ sk_A) = (sk_D))),
% 5.38/5.55      inference('demod', [status(thm)], ['14', '19'])).
% 5.38/5.55  thf(t41_xboole_1, axiom,
% 5.38/5.55    (![A:$i,B:$i,C:$i]:
% 5.38/5.55     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 5.38/5.55       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 5.38/5.55  thf('21', plain,
% 5.38/5.55      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.38/5.55         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 5.38/5.55           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 5.38/5.55      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.38/5.55  thf('22', plain,
% 5.38/5.55      (![X0 : $i]:
% 5.38/5.55         ((k4_xboole_0 @ sk_D @ X0)
% 5.38/5.55           = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_A @ X0)))),
% 5.38/5.55      inference('sup+', [status(thm)], ['20', '21'])).
% 5.38/5.55  thf(t48_xboole_1, axiom,
% 5.38/5.55    (![A:$i,B:$i]:
% 5.38/5.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.38/5.55  thf('23', plain,
% 5.38/5.55      (![X16 : $i, X17 : $i]:
% 5.38/5.55         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.38/5.55           = (k3_xboole_0 @ X16 @ X17))),
% 5.38/5.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.38/5.55  thf('24', plain,
% 5.38/5.55      (![X0 : $i]:
% 5.38/5.55         ((k4_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_D @ X0))
% 5.38/5.55           = (k3_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_A @ X0)))),
% 5.38/5.55      inference('sup+', [status(thm)], ['22', '23'])).
% 5.38/5.55  thf('25', plain,
% 5.38/5.55      (![X16 : $i, X17 : $i]:
% 5.38/5.55         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.38/5.55           = (k3_xboole_0 @ X16 @ X17))),
% 5.38/5.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.38/5.55  thf('26', plain,
% 5.38/5.55      (![X0 : $i]:
% 5.38/5.55         ((k3_xboole_0 @ sk_D @ X0)
% 5.38/5.55           = (k3_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_A @ X0)))),
% 5.38/5.55      inference('demod', [status(thm)], ['24', '25'])).
% 5.38/5.55  thf('27', plain,
% 5.38/5.55      (![X2 : $i, X4 : $i]:
% 5.38/5.55         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 5.38/5.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.38/5.55  thf('28', plain,
% 5.38/5.55      (![X0 : $i]:
% 5.38/5.55         (((k3_xboole_0 @ sk_D @ X0) != (k1_xboole_0))
% 5.38/5.55          | (r1_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_A @ X0)))),
% 5.38/5.55      inference('sup-', [status(thm)], ['26', '27'])).
% 5.38/5.55  thf('29', plain,
% 5.38/5.55      ((((k1_xboole_0) != (k1_xboole_0))
% 5.38/5.55        | (r1_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 5.38/5.55      inference('sup-', [status(thm)], ['7', '28'])).
% 5.38/5.55  thf('30', plain, ((r1_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_A @ sk_B))),
% 5.38/5.55      inference('simplify', [status(thm)], ['29'])).
% 5.38/5.55  thf('31', plain,
% 5.38/5.55      (![X5 : $i, X6 : $i]:
% 5.38/5.55         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 5.38/5.55      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.38/5.55  thf('32', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_D)),
% 5.38/5.55      inference('sup-', [status(thm)], ['30', '31'])).
% 5.38/5.55  thf('33', plain,
% 5.38/5.55      (![X2 : $i, X3 : $i]:
% 5.38/5.55         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 5.38/5.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.38/5.55  thf('34', plain,
% 5.38/5.55      (((k3_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_D) = (k1_xboole_0))),
% 5.38/5.55      inference('sup-', [status(thm)], ['32', '33'])).
% 5.38/5.55  thf('35', plain,
% 5.38/5.55      (![X7 : $i, X8 : $i]:
% 5.38/5.55         ((k4_xboole_0 @ X7 @ X8)
% 5.38/5.55           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 5.38/5.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.38/5.55  thf('36', plain,
% 5.38/5.55      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_D)
% 5.38/5.55         = (k5_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0))),
% 5.38/5.55      inference('sup+', [status(thm)], ['34', '35'])).
% 5.38/5.55  thf('37', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.38/5.55      inference('sup+', [status(thm)], ['17', '18'])).
% 5.38/5.56  thf('38', plain,
% 5.38/5.56      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_D)
% 5.38/5.56         = (k2_xboole_0 @ sk_A @ sk_B))),
% 5.38/5.56      inference('demod', [status(thm)], ['36', '37'])).
% 5.38/5.56  thf('39', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.38/5.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.38/5.56  thf('40', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.38/5.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.38/5.56  thf('41', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 5.38/5.56      inference('cnf', [status(esa)], [t3_boole])).
% 5.38/5.56  thf('42', plain,
% 5.38/5.56      (![X16 : $i, X17 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.38/5.56           = (k3_xboole_0 @ X16 @ X17))),
% 5.38/5.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.38/5.56  thf('43', plain,
% 5.38/5.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 5.38/5.56      inference('sup+', [status(thm)], ['41', '42'])).
% 5.38/5.56  thf('44', plain,
% 5.38/5.56      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 5.38/5.56      inference('cnf', [status(esa)], [t2_boole])).
% 5.38/5.56  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.38/5.56      inference('demod', [status(thm)], ['43', '44'])).
% 5.38/5.56  thf('46', plain,
% 5.38/5.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 5.38/5.56           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.38/5.56  thf('47', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 5.38/5.56           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.38/5.56      inference('sup+', [status(thm)], ['45', '46'])).
% 5.38/5.56  thf('48', plain,
% 5.38/5.56      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 5.38/5.56      inference('cnf', [status(esa)], [t2_boole])).
% 5.38/5.56  thf('49', plain,
% 5.38/5.56      (![X2 : $i, X4 : $i]:
% 5.38/5.56         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 5.38/5.56      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.38/5.56  thf('50', plain,
% 5.38/5.56      (![X0 : $i]:
% 5.38/5.56         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 5.38/5.56      inference('sup-', [status(thm)], ['48', '49'])).
% 5.38/5.56  thf('51', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 5.38/5.56      inference('simplify', [status(thm)], ['50'])).
% 5.38/5.56  thf('52', plain,
% 5.38/5.56      (![X5 : $i, X6 : $i]:
% 5.38/5.56         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 5.38/5.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.38/5.56  thf('53', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 5.38/5.56      inference('sup-', [status(thm)], ['51', '52'])).
% 5.38/5.56  thf('54', plain,
% 5.38/5.56      (![X2 : $i, X3 : $i]:
% 5.38/5.56         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 5.38/5.56      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.38/5.56  thf('55', plain,
% 5.38/5.56      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 5.38/5.56      inference('sup-', [status(thm)], ['53', '54'])).
% 5.38/5.56  thf('56', plain,
% 5.38/5.56      (![X7 : $i, X8 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ X7 @ X8)
% 5.38/5.56           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.38/5.56  thf('57', plain,
% 5.38/5.56      (![X0 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 5.38/5.56           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 5.38/5.56      inference('sup+', [status(thm)], ['55', '56'])).
% 5.38/5.56  thf('58', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.38/5.56      inference('sup+', [status(thm)], ['17', '18'])).
% 5.38/5.56  thf('59', plain,
% 5.38/5.56      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 5.38/5.56      inference('demod', [status(thm)], ['57', '58'])).
% 5.38/5.56  thf('60', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.38/5.56      inference('demod', [status(thm)], ['47', '59'])).
% 5.38/5.56  thf('61', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.38/5.56      inference('sup+', [status(thm)], ['40', '60'])).
% 5.38/5.56  thf(t98_xboole_1, axiom,
% 5.38/5.56    (![A:$i,B:$i]:
% 5.38/5.56     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 5.38/5.56  thf('62', plain,
% 5.38/5.56      (![X18 : $i, X19 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X18 @ X19)
% 5.38/5.56           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 5.38/5.56  thf('63', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 5.38/5.56           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 5.38/5.56      inference('sup+', [status(thm)], ['61', '62'])).
% 5.38/5.56  thf('64', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.38/5.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.38/5.56  thf('65', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.38/5.56      inference('sup+', [status(thm)], ['17', '18'])).
% 5.38/5.56  thf('66', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 5.38/5.56           = (k2_xboole_0 @ X1 @ X0))),
% 5.38/5.56      inference('demod', [status(thm)], ['63', '64', '65'])).
% 5.38/5.56  thf('67', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 5.38/5.56           = (k2_xboole_0 @ X0 @ X1))),
% 5.38/5.56      inference('sup+', [status(thm)], ['39', '66'])).
% 5.38/5.56  thf(t47_xboole_1, axiom,
% 5.38/5.56    (![A:$i,B:$i]:
% 5.38/5.56     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 5.38/5.56  thf('68', plain,
% 5.38/5.56      (![X14 : $i, X15 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 5.38/5.56           = (k4_xboole_0 @ X14 @ X15))),
% 5.38/5.56      inference('cnf', [status(esa)], [t47_xboole_1])).
% 5.38/5.56  thf('69', plain,
% 5.38/5.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 5.38/5.56           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.38/5.56  thf('70', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 5.38/5.56           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 5.38/5.56      inference('sup+', [status(thm)], ['68', '69'])).
% 5.38/5.56  thf('71', plain,
% 5.38/5.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 5.38/5.56           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.38/5.56  thf('72', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 5.38/5.56           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 5.38/5.56      inference('demod', [status(thm)], ['70', '71'])).
% 5.38/5.56  thf('73', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ X1 @ 
% 5.38/5.56           (k2_xboole_0 @ X0 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))
% 5.38/5.56           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 5.38/5.56      inference('sup+', [status(thm)], ['67', '72'])).
% 5.38/5.56  thf('74', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.38/5.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.38/5.56  thf('75', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 5.38/5.56           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 5.38/5.56      inference('demod', [status(thm)], ['70', '71'])).
% 5.38/5.56  thf('76', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 5.38/5.56           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 5.38/5.56      inference('sup+', [status(thm)], ['74', '75'])).
% 5.38/5.56  thf('77', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ X1 @ 
% 5.38/5.56           (k2_xboole_0 @ X0 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))
% 5.38/5.56           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 5.38/5.56      inference('demod', [status(thm)], ['73', '76'])).
% 5.38/5.56  thf('78', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.38/5.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.38/5.56  thf('79', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.38/5.56      inference('demod', [status(thm)], ['47', '59'])).
% 5.38/5.56  thf('80', plain,
% 5.38/5.56      (![X18 : $i, X19 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X18 @ X19)
% 5.38/5.56           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 5.38/5.56  thf('81', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 5.38/5.56           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 5.38/5.56      inference('sup+', [status(thm)], ['79', '80'])).
% 5.38/5.56  thf('82', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.38/5.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.38/5.56  thf('83', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.38/5.56      inference('sup+', [status(thm)], ['17', '18'])).
% 5.38/5.56  thf('84', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 5.38/5.56           = (k2_xboole_0 @ X1 @ X0))),
% 5.38/5.56      inference('demod', [status(thm)], ['81', '82', '83'])).
% 5.38/5.56  thf('85', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 5.38/5.56           = (k2_xboole_0 @ X0 @ X1))),
% 5.38/5.56      inference('sup+', [status(thm)], ['78', '84'])).
% 5.38/5.56  thf('86', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 5.38/5.56           = (k2_xboole_0 @ X0 @ X1))),
% 5.38/5.56      inference('sup+', [status(thm)], ['78', '84'])).
% 5.38/5.56  thf('87', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 5.38/5.56           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1))),
% 5.38/5.56      inference('sup+', [status(thm)], ['85', '86'])).
% 5.38/5.56  thf('88', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.38/5.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.38/5.56  thf('89', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 5.38/5.56           = (k2_xboole_0 @ X0 @ X1))),
% 5.38/5.56      inference('sup+', [status(thm)], ['78', '84'])).
% 5.38/5.56  thf('90', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 5.38/5.56           = (k2_xboole_0 @ X1 @ X0))),
% 5.38/5.56      inference('demod', [status(thm)], ['87', '88', '89'])).
% 5.38/5.56  thf('91', plain,
% 5.38/5.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 5.38/5.56           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.38/5.56  thf('92', plain,
% 5.38/5.56      (![X16 : $i, X17 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.38/5.56           = (k3_xboole_0 @ X16 @ X17))),
% 5.38/5.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.38/5.56  thf('93', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ X2 @ 
% 5.38/5.56           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 5.38/5.56           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 5.38/5.56      inference('sup+', [status(thm)], ['91', '92'])).
% 5.38/5.56  thf('94', plain,
% 5.38/5.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 5.38/5.56           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.38/5.56  thf('95', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ X2 @ 
% 5.38/5.56           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 5.38/5.56           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 5.38/5.56      inference('demod', [status(thm)], ['93', '94'])).
% 5.38/5.56  thf('96', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ X2 @ 
% 5.38/5.56           (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ 
% 5.38/5.56            (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 5.38/5.56           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)) @ 
% 5.38/5.56              (k2_xboole_0 @ X1 @ X0)))),
% 5.38/5.56      inference('sup+', [status(thm)], ['90', '95'])).
% 5.38/5.56  thf('97', plain,
% 5.38/5.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 5.38/5.56           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.38/5.56  thf('98', plain,
% 5.38/5.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 5.38/5.56           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.38/5.56  thf('99', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 5.38/5.56           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X0 @ X3)))),
% 5.38/5.56      inference('sup+', [status(thm)], ['97', '98'])).
% 5.38/5.56  thf('100', plain,
% 5.38/5.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 5.38/5.56           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.38/5.56  thf('101', plain,
% 5.38/5.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 5.38/5.56           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.38/5.56  thf('102', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 5.38/5.56           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 5.38/5.56      inference('demod', [status(thm)], ['99', '100', '101'])).
% 5.38/5.56  thf('103', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ X2 @ 
% 5.38/5.56           (k2_xboole_0 @ X0 @ 
% 5.38/5.56            (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))
% 5.38/5.56           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)) @ 
% 5.38/5.56              (k2_xboole_0 @ X1 @ X0)))),
% 5.38/5.56      inference('demod', [status(thm)], ['96', '102'])).
% 5.38/5.56  thf('104', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ X1 @ 
% 5.38/5.56           (k2_xboole_0 @ X0 @ 
% 5.38/5.56            (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))))
% 5.38/5.56           = (k3_xboole_0 @ 
% 5.38/5.56              (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 5.38/5.56              (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)))),
% 5.38/5.56      inference('sup+', [status(thm)], ['77', '103'])).
% 5.38/5.56  thf('105', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.38/5.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.38/5.56  thf('106', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.38/5.56      inference('demod', [status(thm)], ['43', '44'])).
% 5.38/5.56  thf('107', plain,
% 5.38/5.56      (![X18 : $i, X19 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X18 @ X19)
% 5.38/5.56           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 5.38/5.56  thf('108', plain,
% 5.38/5.56      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.38/5.56      inference('sup+', [status(thm)], ['106', '107'])).
% 5.38/5.56  thf('109', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.38/5.56      inference('sup+', [status(thm)], ['17', '18'])).
% 5.38/5.56  thf('110', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 5.38/5.56      inference('demod', [status(thm)], ['108', '109'])).
% 5.38/5.56  thf('111', plain,
% 5.38/5.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 5.38/5.56           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.38/5.56  thf('112', plain,
% 5.38/5.56      (![X18 : $i, X19 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X18 @ X19)
% 5.38/5.56           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 5.38/5.56  thf('113', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 5.38/5.56           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 5.38/5.56      inference('sup+', [status(thm)], ['111', '112'])).
% 5.38/5.56  thf('114', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 5.38/5.56           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.38/5.56      inference('sup+', [status(thm)], ['110', '113'])).
% 5.38/5.56  thf('115', plain,
% 5.38/5.56      (![X18 : $i, X19 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X18 @ X19)
% 5.38/5.56           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 5.38/5.56  thf('116', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 5.38/5.56           = (k2_xboole_0 @ X0 @ X1))),
% 5.38/5.56      inference('demod', [status(thm)], ['114', '115'])).
% 5.38/5.56  thf('117', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.38/5.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.38/5.56  thf('118', plain,
% 5.38/5.56      (![X16 : $i, X17 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.38/5.56           = (k3_xboole_0 @ X16 @ X17))),
% 5.38/5.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.38/5.56  thf('119', plain,
% 5.38/5.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 5.38/5.56           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.38/5.56  thf('120', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 5.38/5.56           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 5.38/5.56      inference('sup+', [status(thm)], ['118', '119'])).
% 5.38/5.56  thf('121', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 5.38/5.56           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 5.38/5.56      inference('sup+', [status(thm)], ['117', '120'])).
% 5.38/5.56  thf('122', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)
% 5.38/5.56           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.38/5.56      inference('sup+', [status(thm)], ['116', '121'])).
% 5.38/5.56  thf('123', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.38/5.56      inference('sup+', [status(thm)], ['40', '60'])).
% 5.38/5.56  thf('124', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1) = (k1_xboole_0))),
% 5.38/5.56      inference('demod', [status(thm)], ['122', '123'])).
% 5.38/5.56  thf('125', plain,
% 5.38/5.56      (![X18 : $i, X19 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X18 @ X19)
% 5.38/5.56           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 5.38/5.56  thf('126', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 5.38/5.56           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.38/5.56      inference('sup+', [status(thm)], ['124', '125'])).
% 5.38/5.56  thf('127', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.38/5.56      inference('sup+', [status(thm)], ['17', '18'])).
% 5.38/5.56  thf('128', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 5.38/5.56      inference('demod', [status(thm)], ['126', '127'])).
% 5.38/5.56  thf('129', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 5.38/5.56           = (k2_xboole_0 @ X0 @ X1))),
% 5.38/5.56      inference('demod', [status(thm)], ['114', '115'])).
% 5.38/5.56  thf('130', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.38/5.56      inference('sup+', [status(thm)], ['40', '60'])).
% 5.38/5.56  thf('131', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 5.38/5.56      inference('demod', [status(thm)], ['126', '127'])).
% 5.38/5.56  thf('132', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.38/5.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.38/5.56  thf('133', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 5.38/5.56      inference('demod', [status(thm)], ['126', '127'])).
% 5.38/5.56  thf('134', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k1_xboole_0) = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 5.38/5.56      inference('demod', [status(thm)],
% 5.38/5.56                ['104', '105', '128', '129', '130', '131', '132', '133'])).
% 5.38/5.56  thf('135', plain,
% 5.38/5.56      (![X2 : $i, X4 : $i]:
% 5.38/5.56         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 5.38/5.56      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.38/5.56  thf('136', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         (((k1_xboole_0) != (k1_xboole_0))
% 5.38/5.56          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 5.38/5.56      inference('sup-', [status(thm)], ['134', '135'])).
% 5.38/5.56  thf('137', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 5.38/5.56      inference('simplify', [status(thm)], ['136'])).
% 5.38/5.56  thf('138', plain,
% 5.38/5.56      (![X5 : $i, X6 : $i]:
% 5.38/5.56         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 5.38/5.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.38/5.56  thf('139', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 5.38/5.56      inference('sup-', [status(thm)], ['137', '138'])).
% 5.38/5.56  thf('140', plain,
% 5.38/5.56      (![X2 : $i, X3 : $i]:
% 5.38/5.56         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 5.38/5.56      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.38/5.56  thf('141', plain,
% 5.38/5.56      (![X0 : $i, X1 : $i]:
% 5.38/5.56         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 5.38/5.56      inference('sup-', [status(thm)], ['139', '140'])).
% 5.38/5.56  thf('142', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 5.38/5.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.38/5.56  thf('143', plain,
% 5.38/5.56      (![X5 : $i, X6 : $i]:
% 5.38/5.56         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 5.38/5.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.38/5.56  thf('144', plain, ((r1_xboole_0 @ sk_D @ sk_C)),
% 5.38/5.56      inference('sup-', [status(thm)], ['142', '143'])).
% 5.38/5.56  thf('145', plain,
% 5.38/5.56      (![X2 : $i, X3 : $i]:
% 5.38/5.56         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 5.38/5.56      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.38/5.56  thf('146', plain, (((k3_xboole_0 @ sk_D @ sk_C) = (k1_xboole_0))),
% 5.38/5.56      inference('sup-', [status(thm)], ['144', '145'])).
% 5.38/5.56  thf('147', plain,
% 5.38/5.56      (![X7 : $i, X8 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ X7 @ X8)
% 5.38/5.56           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.38/5.56  thf('148', plain,
% 5.38/5.56      (((k4_xboole_0 @ sk_D @ sk_C) = (k5_xboole_0 @ sk_D @ k1_xboole_0))),
% 5.38/5.56      inference('sup+', [status(thm)], ['146', '147'])).
% 5.38/5.56  thf('149', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.38/5.56      inference('sup+', [status(thm)], ['17', '18'])).
% 5.38/5.56  thf('150', plain, (((k4_xboole_0 @ sk_D @ sk_C) = (sk_D))),
% 5.38/5.56      inference('demod', [status(thm)], ['148', '149'])).
% 5.38/5.56  thf('151', plain,
% 5.38/5.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 5.38/5.56           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 5.38/5.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.38/5.56  thf('152', plain,
% 5.38/5.56      (![X0 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ sk_D @ X0)
% 5.38/5.56           = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_C @ X0)))),
% 5.38/5.56      inference('sup+', [status(thm)], ['150', '151'])).
% 5.38/5.56  thf('153', plain,
% 5.38/5.56      (![X16 : $i, X17 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.38/5.56           = (k3_xboole_0 @ X16 @ X17))),
% 5.38/5.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.38/5.56  thf('154', plain,
% 5.38/5.56      (![X0 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_D @ X0))
% 5.38/5.56           = (k3_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_C @ X0)))),
% 5.38/5.56      inference('sup+', [status(thm)], ['152', '153'])).
% 5.38/5.56  thf('155', plain,
% 5.38/5.56      (![X16 : $i, X17 : $i]:
% 5.38/5.56         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.38/5.56           = (k3_xboole_0 @ X16 @ X17))),
% 5.38/5.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.38/5.56  thf('156', plain,
% 5.38/5.56      (![X0 : $i]:
% 5.38/5.56         ((k3_xboole_0 @ sk_D @ X0)
% 5.38/5.56           = (k3_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_C @ X0)))),
% 5.38/5.56      inference('demod', [status(thm)], ['154', '155'])).
% 5.38/5.56  thf('157', plain,
% 5.38/5.56      (![X2 : $i, X4 : $i]:
% 5.38/5.56         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 5.38/5.56      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.38/5.56  thf('158', plain,
% 5.38/5.56      (![X0 : $i]:
% 5.38/5.56         (((k3_xboole_0 @ sk_D @ X0) != (k1_xboole_0))
% 5.38/5.56          | (r1_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_C @ X0)))),
% 5.38/5.56      inference('sup-', [status(thm)], ['156', '157'])).
% 5.38/5.56  thf('159', plain,
% 5.38/5.56      (![X0 : $i]:
% 5.38/5.56         (((k1_xboole_0) != (k1_xboole_0))
% 5.38/5.56          | (r1_xboole_0 @ sk_D @ 
% 5.38/5.56             (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ X0 @ sk_D))))),
% 5.38/5.56      inference('sup-', [status(thm)], ['141', '158'])).
% 5.38/5.56  thf('160', plain,
% 5.38/5.56      (![X0 : $i]:
% 5.38/5.56         (r1_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ X0 @ sk_D)))),
% 5.38/5.56      inference('simplify', [status(thm)], ['159'])).
% 5.38/5.56  thf('161', plain,
% 5.38/5.56      ((r1_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 5.38/5.56      inference('sup+', [status(thm)], ['38', '160'])).
% 5.38/5.56  thf('162', plain,
% 5.38/5.56      (![X5 : $i, X6 : $i]:
% 5.38/5.56         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 5.38/5.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.38/5.56  thf('163', plain,
% 5.38/5.56      ((r1_xboole_0 @ (k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B)) @ sk_D)),
% 5.38/5.56      inference('sup-', [status(thm)], ['161', '162'])).
% 5.38/5.56  thf('164', plain, ($false), inference('demod', [status(thm)], ['2', '163'])).
% 5.38/5.56  
% 5.38/5.56  % SZS output end Refutation
% 5.38/5.56  
% 5.38/5.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
