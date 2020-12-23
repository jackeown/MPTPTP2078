%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aEVH6VNtDz

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:01 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 317 expanded)
%              Number of leaves         :   21 ( 112 expanded)
%              Depth                    :   22
%              Number of atoms          :  996 (2426 expanded)
%              Number of equality atoms :  112 ( 296 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('5',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_D )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['12','23'])).

thf('25',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_C )
    = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('43',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = sk_C ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35','38','47'])).

thf('49',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r1_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['50'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('53',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('55',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('57',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) @ sk_C ) )
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('59',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('66',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['57','64','65'])).

thf('67',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('68',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('70',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('73',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('76',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('78',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B ) )
    = sk_D ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('80',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k4_xboole_0 @ sk_D @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['73','80'])).

thf('82',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('83',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('86',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('87',plain,(
    ! [X22: $i,X23: $i,X25: $i] :
      ( ( r1_xboole_0 @ X22 @ X25 )
      | ~ ( r1_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_A )
      | ( r1_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference('sup-',[status(thm)],['70','88'])).

thf('90',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('91',plain,(
    r1_xboole_0 @ sk_D @ sk_C ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) )
      | ~ ( r1_xboole_0 @ X22 @ X23 )
      | ~ ( r1_xboole_0 @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_D @ X0 )
      | ( r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    r1_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('97',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('98',plain,(
    ! [X22: $i,X23: $i,X25: $i] :
      ( ( r1_xboole_0 @ X22 @ X25 )
      | ~ ( r1_xboole_0 @ X22 @ ( k2_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    r1_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('103',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_D ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('105',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('107',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_D ) )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('112',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['107','108','109','110','111'])).

thf('113',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('114',plain,
    ( ( k2_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('117',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    sk_B = sk_C ),
    inference(demod,[status(thm)],['68','69','117'])).

thf('119',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['118','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aEVH6VNtDz
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.70/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.89  % Solved by: fo/fo7.sh
% 0.70/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.89  % done 894 iterations in 0.427s
% 0.70/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.89  % SZS output start Refutation
% 0.70/0.89  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.70/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.70/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.89  thf(sk_D_type, type, sk_D: $i).
% 0.70/0.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(t3_boole, axiom,
% 0.70/0.89    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.70/0.89  thf('0', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.70/0.89      inference('cnf', [status(esa)], [t3_boole])).
% 0.70/0.89  thf(t48_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.70/0.89  thf('1', plain,
% 0.70/0.89      (![X15 : $i, X16 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.70/0.89           = (k3_xboole_0 @ X15 @ X16))),
% 0.70/0.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.70/0.89  thf('2', plain,
% 0.70/0.89      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['0', '1'])).
% 0.70/0.89  thf(t2_boole, axiom,
% 0.70/0.89    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.70/0.89  thf('3', plain,
% 0.70/0.89      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.89      inference('cnf', [status(esa)], [t2_boole])).
% 0.70/0.89  thf('4', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.89      inference('demod', [status(thm)], ['2', '3'])).
% 0.70/0.89  thf(t72_xboole_1, conjecture,
% 0.70/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.89     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.70/0.89         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.70/0.89       ( ( C ) = ( B ) ) ))).
% 0.70/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.89    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.89        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.70/0.89            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.70/0.89          ( ( C ) = ( B ) ) ) )),
% 0.70/0.89    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.70/0.89  thf('5', plain,
% 0.70/0.89      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(commutativity_k2_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.70/0.89  thf('6', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.89  thf('7', plain,
% 0.70/0.89      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.70/0.89      inference('demod', [status(thm)], ['5', '6'])).
% 0.70/0.89  thf(t41_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.70/0.89       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.70/0.89  thf('8', plain,
% 0.70/0.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.70/0.89           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.70/0.89  thf('9', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 0.70/0.89           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['7', '8'])).
% 0.70/0.89  thf('10', plain,
% 0.70/0.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.70/0.89           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.70/0.89  thf('11', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 0.70/0.89           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.70/0.89      inference('demod', [status(thm)], ['9', '10'])).
% 0.70/0.89  thf('12', plain,
% 0.70/0.89      (((k4_xboole_0 @ k1_xboole_0 @ sk_D)
% 0.70/0.89         = (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 0.70/0.89      inference('sup+', [status(thm)], ['4', '11'])).
% 0.70/0.89  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.89      inference('demod', [status(thm)], ['2', '3'])).
% 0.70/0.89  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.89      inference('demod', [status(thm)], ['2', '3'])).
% 0.70/0.89  thf(t39_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.70/0.89  thf('15', plain,
% 0.70/0.89      (![X9 : $i, X10 : $i]:
% 0.70/0.89         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.70/0.89           = (k2_xboole_0 @ X9 @ X10))),
% 0.70/0.89      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.70/0.89  thf('16', plain,
% 0.70/0.89      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['14', '15'])).
% 0.70/0.89  thf(t1_boole, axiom,
% 0.70/0.89    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.70/0.89  thf('17', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.70/0.89      inference('cnf', [status(esa)], [t1_boole])).
% 0.70/0.89  thf('18', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.70/0.89      inference('demod', [status(thm)], ['16', '17'])).
% 0.70/0.89  thf('19', plain,
% 0.70/0.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.70/0.89           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.70/0.89  thf('20', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.70/0.89           = (k4_xboole_0 @ X1 @ X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['18', '19'])).
% 0.70/0.89  thf('21', plain,
% 0.70/0.89      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['13', '20'])).
% 0.70/0.89  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.89      inference('demod', [status(thm)], ['2', '3'])).
% 0.70/0.89  thf('23', plain,
% 0.70/0.89      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.70/0.89      inference('demod', [status(thm)], ['21', '22'])).
% 0.70/0.89  thf('24', plain,
% 0.70/0.89      (((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 0.70/0.89      inference('demod', [status(thm)], ['12', '23'])).
% 0.70/0.89  thf('25', plain,
% 0.70/0.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.70/0.89           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.70/0.89  thf('26', plain,
% 0.70/0.89      (![X15 : $i, X16 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.70/0.89           = (k3_xboole_0 @ X15 @ X16))),
% 0.70/0.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.70/0.89  thf('27', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 0.70/0.89           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['25', '26'])).
% 0.70/0.89  thf('28', plain,
% 0.70/0.89      (((k4_xboole_0 @ sk_C @ k1_xboole_0)
% 0.70/0.89         = (k3_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['24', '27'])).
% 0.70/0.89  thf('29', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.70/0.89      inference('cnf', [status(esa)], [t3_boole])).
% 0.70/0.89  thf('30', plain,
% 0.70/0.89      (((sk_C) = (k3_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.70/0.89      inference('demod', [status(thm)], ['28', '29'])).
% 0.70/0.89  thf('31', plain,
% 0.70/0.89      (![X15 : $i, X16 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.70/0.89           = (k3_xboole_0 @ X15 @ X16))),
% 0.70/0.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.70/0.89  thf('32', plain,
% 0.70/0.89      (![X15 : $i, X16 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.70/0.89           = (k3_xboole_0 @ X15 @ X16))),
% 0.70/0.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.70/0.89  thf('33', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.70/0.89           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['31', '32'])).
% 0.70/0.89  thf('34', plain,
% 0.70/0.89      (((k4_xboole_0 @ sk_C @ sk_C)
% 0.70/0.89         = (k3_xboole_0 @ sk_C @ 
% 0.70/0.89            (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_A))))),
% 0.70/0.89      inference('sup+', [status(thm)], ['30', '33'])).
% 0.70/0.89  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.89      inference('demod', [status(thm)], ['2', '3'])).
% 0.70/0.89  thf('36', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.89  thf('37', plain,
% 0.70/0.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.70/0.89           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.70/0.89  thf('38', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 0.70/0.89           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['36', '37'])).
% 0.70/0.89  thf('39', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(d7_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.70/0.89       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.70/0.89  thf('40', plain,
% 0.70/0.89      (![X2 : $i, X3 : $i]:
% 0.70/0.89         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.70/0.89      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.70/0.89  thf('41', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['39', '40'])).
% 0.70/0.89  thf(t51_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.70/0.89       ( A ) ))).
% 0.70/0.89  thf('42', plain,
% 0.70/0.89      (![X20 : $i, X21 : $i]:
% 0.70/0.89         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 0.70/0.89           = (X20))),
% 0.70/0.89      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.70/0.89  thf('43', plain,
% 0.70/0.89      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A)) = (sk_C))),
% 0.70/0.89      inference('sup+', [status(thm)], ['41', '42'])).
% 0.70/0.89  thf('44', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.89  thf('45', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.70/0.89      inference('cnf', [status(esa)], [t1_boole])).
% 0.70/0.89  thf('46', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['44', '45'])).
% 0.70/0.89  thf('47', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.70/0.89      inference('demod', [status(thm)], ['43', '46'])).
% 0.70/0.89  thf('48', plain,
% 0.70/0.89      (((k1_xboole_0) = (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_B)))),
% 0.70/0.89      inference('demod', [status(thm)], ['34', '35', '38', '47'])).
% 0.70/0.89  thf('49', plain,
% 0.70/0.89      (![X2 : $i, X4 : $i]:
% 0.70/0.89         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.70/0.89      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.70/0.89  thf('50', plain,
% 0.70/0.89      ((((k1_xboole_0) != (k1_xboole_0))
% 0.70/0.89        | (r1_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_B)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['48', '49'])).
% 0.70/0.89  thf('51', plain, ((r1_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_B))),
% 0.70/0.89      inference('simplify', [status(thm)], ['50'])).
% 0.70/0.89  thf(symmetry_r1_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.70/0.89  thf('52', plain,
% 0.70/0.89      (![X5 : $i, X6 : $i]:
% 0.70/0.89         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.70/0.89      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.70/0.89  thf('53', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B) @ sk_C)),
% 0.70/0.89      inference('sup-', [status(thm)], ['51', '52'])).
% 0.70/0.89  thf('54', plain,
% 0.70/0.89      (![X2 : $i, X3 : $i]:
% 0.70/0.89         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.70/0.89      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.70/0.89  thf('55', plain,
% 0.70/0.89      (((k3_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['53', '54'])).
% 0.70/0.89  thf('56', plain,
% 0.70/0.89      (![X20 : $i, X21 : $i]:
% 0.70/0.89         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 0.70/0.89           = (X20))),
% 0.70/0.89      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.70/0.89  thf('57', plain,
% 0.70/0.89      (((k2_xboole_0 @ k1_xboole_0 @ 
% 0.70/0.89         (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B) @ sk_C))
% 0.70/0.89         = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.70/0.89      inference('sup+', [status(thm)], ['55', '56'])).
% 0.70/0.89  thf('58', plain,
% 0.70/0.89      (![X9 : $i, X10 : $i]:
% 0.70/0.89         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.70/0.89           = (k2_xboole_0 @ X9 @ X10))),
% 0.70/0.89      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.70/0.89  thf('59', plain,
% 0.70/0.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.70/0.89           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.70/0.89  thf('60', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 0.70/0.89           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['58', '59'])).
% 0.70/0.89  thf('61', plain,
% 0.70/0.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.70/0.89           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.70/0.89  thf('62', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 0.70/0.89           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.70/0.89      inference('demod', [status(thm)], ['60', '61'])).
% 0.70/0.89  thf('63', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.89      inference('demod', [status(thm)], ['2', '3'])).
% 0.70/0.89  thf('64', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['62', '63'])).
% 0.70/0.89  thf('65', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['44', '45'])).
% 0.70/0.89  thf('66', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.70/0.89      inference('demod', [status(thm)], ['57', '64', '65'])).
% 0.70/0.89  thf('67', plain,
% 0.70/0.89      (![X9 : $i, X10 : $i]:
% 0.70/0.89         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.70/0.89           = (k2_xboole_0 @ X9 @ X10))),
% 0.70/0.89      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.70/0.89  thf('68', plain,
% 0.70/0.89      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.70/0.89      inference('sup+', [status(thm)], ['66', '67'])).
% 0.70/0.89  thf('69', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.70/0.89      inference('cnf', [status(esa)], [t1_boole])).
% 0.70/0.89  thf('70', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('71', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 0.70/0.89           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.70/0.89      inference('demod', [status(thm)], ['9', '10'])).
% 0.70/0.89  thf('72', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['62', '63'])).
% 0.70/0.89  thf('73', plain,
% 0.70/0.89      (((k4_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A) = (k1_xboole_0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['71', '72'])).
% 0.70/0.89  thf('74', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('75', plain,
% 0.70/0.89      (![X2 : $i, X3 : $i]:
% 0.70/0.89         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.70/0.89      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.70/0.89  thf('76', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['74', '75'])).
% 0.70/0.89  thf('77', plain,
% 0.70/0.89      (![X20 : $i, X21 : $i]:
% 0.70/0.89         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 0.70/0.89           = (X20))),
% 0.70/0.89      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.70/0.89  thf('78', plain,
% 0.70/0.89      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B)) = (sk_D))),
% 0.70/0.89      inference('sup+', [status(thm)], ['76', '77'])).
% 0.70/0.89  thf('79', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['44', '45'])).
% 0.70/0.89  thf('80', plain, (((k4_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 0.70/0.89      inference('demod', [status(thm)], ['78', '79'])).
% 0.70/0.89  thf('81', plain, (((k4_xboole_0 @ sk_D @ sk_A) = (k1_xboole_0))),
% 0.70/0.89      inference('demod', [status(thm)], ['73', '80'])).
% 0.70/0.89  thf('82', plain,
% 0.70/0.89      (![X9 : $i, X10 : $i]:
% 0.70/0.89         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.70/0.89           = (k2_xboole_0 @ X9 @ X10))),
% 0.70/0.89      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.70/0.89  thf('83', plain,
% 0.70/0.89      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.70/0.89      inference('sup+', [status(thm)], ['81', '82'])).
% 0.70/0.89  thf('84', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.89  thf('85', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['44', '45'])).
% 0.70/0.89  thf('86', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_D))),
% 0.70/0.89      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.70/0.89  thf(t70_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.70/0.89            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.70/0.89       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.70/0.89            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.70/0.89  thf('87', plain,
% 0.70/0.89      (![X22 : $i, X23 : $i, X25 : $i]:
% 0.70/0.89         ((r1_xboole_0 @ X22 @ X25)
% 0.70/0.89          | ~ (r1_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X25)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.70/0.89  thf('88', plain,
% 0.70/0.89      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ sk_A) | (r1_xboole_0 @ X0 @ sk_D))),
% 0.70/0.89      inference('sup-', [status(thm)], ['86', '87'])).
% 0.70/0.89  thf('89', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.70/0.89      inference('sup-', [status(thm)], ['70', '88'])).
% 0.70/0.89  thf('90', plain,
% 0.70/0.89      (![X5 : $i, X6 : $i]:
% 0.70/0.89         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.70/0.89      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.70/0.89  thf('91', plain, ((r1_xboole_0 @ sk_D @ sk_C)),
% 0.70/0.89      inference('sup-', [status(thm)], ['89', '90'])).
% 0.70/0.89  thf('92', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('93', plain,
% 0.70/0.89      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.70/0.89         ((r1_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X24))
% 0.70/0.89          | ~ (r1_xboole_0 @ X22 @ X23)
% 0.70/0.89          | ~ (r1_xboole_0 @ X22 @ X24))),
% 0.70/0.89      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.70/0.89  thf('94', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (r1_xboole_0 @ sk_D @ X0)
% 0.70/0.89          | (r1_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['92', '93'])).
% 0.70/0.89  thf('95', plain, ((r1_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.70/0.89      inference('sup-', [status(thm)], ['91', '94'])).
% 0.70/0.89  thf('96', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.89  thf('97', plain,
% 0.70/0.89      (![X9 : $i, X10 : $i]:
% 0.70/0.89         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.70/0.89           = (k2_xboole_0 @ X9 @ X10))),
% 0.70/0.89      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.70/0.89  thf('98', plain,
% 0.70/0.89      (![X22 : $i, X23 : $i, X25 : $i]:
% 0.70/0.89         ((r1_xboole_0 @ X22 @ X25)
% 0.70/0.89          | ~ (r1_xboole_0 @ X22 @ (k2_xboole_0 @ X23 @ X25)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.70/0.89  thf('99', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.70/0.89          | (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['97', '98'])).
% 0.70/0.89  thf('100', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.70/0.89          | (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['96', '99'])).
% 0.70/0.89  thf('101', plain, ((r1_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.70/0.89      inference('sup-', [status(thm)], ['95', '100'])).
% 0.70/0.89  thf('102', plain,
% 0.70/0.89      (![X5 : $i, X6 : $i]:
% 0.70/0.89         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.70/0.89      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.70/0.89  thf('103', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_D)),
% 0.70/0.89      inference('sup-', [status(thm)], ['101', '102'])).
% 0.70/0.89  thf('104', plain,
% 0.70/0.89      (![X2 : $i, X3 : $i]:
% 0.70/0.89         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.70/0.89      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.70/0.89  thf('105', plain,
% 0.70/0.89      (((k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_D) = (k1_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['103', '104'])).
% 0.70/0.89  thf('106', plain,
% 0.70/0.89      (![X20 : $i, X21 : $i]:
% 0.70/0.89         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 0.70/0.89           = (X20))),
% 0.70/0.89      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.70/0.89  thf('107', plain,
% 0.70/0.89      (((k2_xboole_0 @ k1_xboole_0 @ 
% 0.70/0.89         (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_D))
% 0.70/0.89         = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.70/0.89      inference('sup+', [status(thm)], ['105', '106'])).
% 0.70/0.89  thf('108', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)
% 0.70/0.89           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 0.70/0.89      inference('demod', [status(thm)], ['9', '10'])).
% 0.70/0.89  thf('109', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.89      inference('demod', [status(thm)], ['2', '3'])).
% 0.70/0.89  thf('110', plain,
% 0.70/0.89      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.70/0.89      inference('demod', [status(thm)], ['21', '22'])).
% 0.70/0.89  thf('111', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['44', '45'])).
% 0.70/0.89  thf('112', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.70/0.89      inference('demod', [status(thm)], ['107', '108', '109', '110', '111'])).
% 0.70/0.89  thf('113', plain,
% 0.70/0.89      (![X9 : $i, X10 : $i]:
% 0.70/0.89         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.70/0.89           = (k2_xboole_0 @ X9 @ X10))),
% 0.70/0.89      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.70/0.89  thf('114', plain,
% 0.70/0.89      (((k2_xboole_0 @ sk_C @ k1_xboole_0) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.70/0.89      inference('sup+', [status(thm)], ['112', '113'])).
% 0.70/0.89  thf('115', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.70/0.89      inference('cnf', [status(esa)], [t1_boole])).
% 0.70/0.89  thf('116', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.89  thf('117', plain, (((sk_C) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.70/0.89      inference('demod', [status(thm)], ['114', '115', '116'])).
% 0.70/0.89  thf('118', plain, (((sk_B) = (sk_C))),
% 0.70/0.89      inference('demod', [status(thm)], ['68', '69', '117'])).
% 0.70/0.89  thf('119', plain, (((sk_C) != (sk_B))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('120', plain, ($false),
% 0.70/0.89      inference('simplify_reflect-', [status(thm)], ['118', '119'])).
% 0.70/0.89  
% 0.70/0.89  % SZS output end Refutation
% 0.70/0.89  
% 0.70/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
