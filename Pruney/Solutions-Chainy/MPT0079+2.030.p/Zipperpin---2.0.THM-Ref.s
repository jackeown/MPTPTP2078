%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.abvnIT20tA

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:00 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 836 expanded)
%              Number of leaves         :   25 ( 278 expanded)
%              Depth                    :   28
%              Number of atoms          :  995 (6565 expanded)
%              Number of equality atoms :  131 ( 865 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_C @ sk_D ) )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_D )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','27'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ sk_D @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('35',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference(simplify,[status(thm)],['40'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('43',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('48',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('52',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_D )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['45','54'])).

thf('56',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_D )
    = sk_C ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = sk_C ),
    inference(demod,[status(thm)],['4','57'])).

thf('59',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_D )
    = sk_C ),
    inference(demod,[status(thm)],['4','57'])).

thf('60',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('65',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X31 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X29 @ X30 ) @ ( k3_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['59','68'])).

thf('70',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('71',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X31 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X29 @ X30 ) @ ( k3_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('74',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('81',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
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

thf('85',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X31 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X29 @ X30 ) @ ( k3_xboole_0 @ X29 @ X31 ) ) ) ),
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
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['69','87'])).

thf('89',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('90',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k4_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('92',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('94',plain,
    ( ( k2_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('98',plain,
    ( sk_D
    = ( k2_xboole_0 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['94','95','96','97'])).

thf('99',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['43','44'])).

thf('100',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('102',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['58','100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('104',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('105',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_D @ X0 )
      = ( k4_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['103','106'])).

thf('108',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('111',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['98','99'])).

thf('113',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    sk_C = sk_B ),
    inference('sup+',[status(thm)],['102','113'])).

thf('115',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['114','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.abvnIT20tA
% 0.13/0.37  % Computer   : n015.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 09:35:53 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 1.37/1.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.37/1.54  % Solved by: fo/fo7.sh
% 1.37/1.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.37/1.54  % done 2081 iterations in 1.055s
% 1.37/1.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.37/1.54  % SZS output start Refutation
% 1.37/1.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.37/1.54  thf(sk_A_type, type, sk_A: $i).
% 1.37/1.54  thf(sk_C_type, type, sk_C: $i).
% 1.37/1.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.37/1.54  thf(sk_D_type, type, sk_D: $i).
% 1.37/1.54  thf(sk_B_type, type, sk_B: $i).
% 1.37/1.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.37/1.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.37/1.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.37/1.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.37/1.54  thf(t72_xboole_1, conjecture,
% 1.37/1.54    (![A:$i,B:$i,C:$i,D:$i]:
% 1.37/1.54     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 1.37/1.54         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 1.37/1.54       ( ( C ) = ( B ) ) ))).
% 1.37/1.54  thf(zf_stmt_0, negated_conjecture,
% 1.37/1.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.37/1.54        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 1.37/1.54            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 1.37/1.54          ( ( C ) = ( B ) ) ) )),
% 1.37/1.54    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 1.37/1.54  thf('0', plain,
% 1.37/1.54      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.37/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.54  thf(commutativity_k2_xboole_0, axiom,
% 1.37/1.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.37/1.54  thf('1', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.37/1.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.37/1.54  thf('2', plain,
% 1.37/1.54      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.37/1.54      inference('demod', [status(thm)], ['0', '1'])).
% 1.37/1.54  thf(t40_xboole_1, axiom,
% 1.37/1.54    (![A:$i,B:$i]:
% 1.37/1.54     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.37/1.54  thf('3', plain,
% 1.37/1.54      (![X15 : $i, X16 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 1.37/1.54           = (k4_xboole_0 @ X15 @ X16))),
% 1.37/1.54      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.37/1.54  thf('4', plain,
% 1.37/1.54      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 1.37/1.54         = (k4_xboole_0 @ sk_C @ sk_D))),
% 1.37/1.54      inference('sup+', [status(thm)], ['2', '3'])).
% 1.37/1.54  thf('5', plain,
% 1.37/1.54      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D)
% 1.37/1.54         = (k4_xboole_0 @ sk_C @ sk_D))),
% 1.37/1.54      inference('sup+', [status(thm)], ['2', '3'])).
% 1.37/1.54  thf(t39_xboole_1, axiom,
% 1.37/1.54    (![A:$i,B:$i]:
% 1.37/1.54     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.37/1.54  thf('6', plain,
% 1.37/1.54      (![X12 : $i, X13 : $i]:
% 1.37/1.54         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 1.37/1.54           = (k2_xboole_0 @ X12 @ X13))),
% 1.37/1.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.37/1.54  thf('7', plain,
% 1.37/1.54      (((k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_C @ sk_D))
% 1.37/1.54         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.37/1.54      inference('sup+', [status(thm)], ['5', '6'])).
% 1.37/1.54  thf('8', plain,
% 1.37/1.54      (![X12 : $i, X13 : $i]:
% 1.37/1.54         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 1.37/1.54           = (k2_xboole_0 @ X12 @ X13))),
% 1.37/1.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.37/1.54  thf('9', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.37/1.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.37/1.54  thf('10', plain,
% 1.37/1.54      (((k2_xboole_0 @ sk_C @ sk_D)
% 1.37/1.54         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.37/1.54      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.37/1.54  thf('11', plain,
% 1.37/1.54      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 1.37/1.54      inference('demod', [status(thm)], ['0', '1'])).
% 1.37/1.54  thf('12', plain,
% 1.37/1.54      (((k2_xboole_0 @ sk_B @ sk_A)
% 1.37/1.54         = (k2_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.37/1.54      inference('demod', [status(thm)], ['10', '11'])).
% 1.37/1.54  thf('13', plain,
% 1.37/1.54      (![X15 : $i, X16 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 1.37/1.54           = (k4_xboole_0 @ X15 @ X16))),
% 1.37/1.54      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.37/1.54  thf('14', plain,
% 1.37/1.54      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ 
% 1.37/1.54         (k2_xboole_0 @ sk_B @ sk_A))
% 1.37/1.54         = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.37/1.54      inference('sup+', [status(thm)], ['12', '13'])).
% 1.37/1.54  thf('15', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.37/1.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.37/1.54  thf(t1_boole, axiom,
% 1.37/1.54    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.37/1.54  thf('16', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.37/1.54      inference('cnf', [status(esa)], [t1_boole])).
% 1.37/1.54  thf('17', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.37/1.54      inference('sup+', [status(thm)], ['15', '16'])).
% 1.37/1.54  thf('18', plain,
% 1.37/1.54      (![X15 : $i, X16 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 1.37/1.54           = (k4_xboole_0 @ X15 @ X16))),
% 1.37/1.54      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.37/1.54  thf('19', plain,
% 1.37/1.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.37/1.54      inference('sup+', [status(thm)], ['17', '18'])).
% 1.37/1.54  thf('20', plain,
% 1.37/1.54      (((k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A))
% 1.37/1.54         = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.37/1.54      inference('demod', [status(thm)], ['14', '19'])).
% 1.37/1.54  thf('21', plain,
% 1.37/1.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.37/1.54      inference('sup+', [status(thm)], ['17', '18'])).
% 1.37/1.54  thf(t3_boole, axiom,
% 1.37/1.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.37/1.54  thf('22', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.37/1.54      inference('cnf', [status(esa)], [t3_boole])).
% 1.37/1.54  thf(t48_xboole_1, axiom,
% 1.37/1.54    (![A:$i,B:$i]:
% 1.37/1.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.37/1.54  thf('23', plain,
% 1.37/1.54      (![X22 : $i, X23 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 1.37/1.54           = (k3_xboole_0 @ X22 @ X23))),
% 1.37/1.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.37/1.54  thf('24', plain,
% 1.37/1.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.37/1.54      inference('sup+', [status(thm)], ['22', '23'])).
% 1.37/1.54  thf(t2_boole, axiom,
% 1.37/1.54    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.37/1.54  thf('25', plain,
% 1.37/1.54      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 1.37/1.54      inference('cnf', [status(esa)], [t2_boole])).
% 1.37/1.54  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.37/1.54      inference('demod', [status(thm)], ['24', '25'])).
% 1.37/1.54  thf('27', plain,
% 1.37/1.54      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.37/1.54      inference('demod', [status(thm)], ['21', '26'])).
% 1.37/1.54  thf('28', plain,
% 1.37/1.54      (((k1_xboole_0) = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 1.37/1.54      inference('demod', [status(thm)], ['20', '27'])).
% 1.37/1.54  thf(t41_xboole_1, axiom,
% 1.37/1.54    (![A:$i,B:$i,C:$i]:
% 1.37/1.54     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.37/1.54       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.37/1.54  thf('29', plain,
% 1.37/1.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 1.37/1.54           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 1.37/1.54      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.37/1.54  thf(l32_xboole_1, axiom,
% 1.37/1.54    (![A:$i,B:$i]:
% 1.37/1.54     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.37/1.54  thf('30', plain,
% 1.37/1.54      (![X5 : $i, X6 : $i]:
% 1.37/1.54         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 1.37/1.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.37/1.54  thf('31', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.54         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 1.37/1.54          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.37/1.54      inference('sup-', [status(thm)], ['29', '30'])).
% 1.37/1.54  thf('32', plain,
% 1.37/1.54      ((((k1_xboole_0) != (k1_xboole_0))
% 1.37/1.54        | (r1_tarski @ (k4_xboole_0 @ sk_D @ sk_B) @ sk_A))),
% 1.37/1.54      inference('sup-', [status(thm)], ['28', '31'])).
% 1.37/1.54  thf('33', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 1.37/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.54  thf(d7_xboole_0, axiom,
% 1.37/1.54    (![A:$i,B:$i]:
% 1.37/1.54     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.37/1.54       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.37/1.54  thf('34', plain,
% 1.37/1.54      (![X2 : $i, X3 : $i]:
% 1.37/1.54         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.37/1.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.37/1.54  thf('35', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 1.37/1.54      inference('sup-', [status(thm)], ['33', '34'])).
% 1.37/1.54  thf(t47_xboole_1, axiom,
% 1.37/1.54    (![A:$i,B:$i]:
% 1.37/1.54     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.37/1.54  thf('36', plain,
% 1.37/1.54      (![X20 : $i, X21 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))
% 1.37/1.54           = (k4_xboole_0 @ X20 @ X21))),
% 1.37/1.54      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.37/1.54  thf('37', plain,
% 1.37/1.54      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_B))),
% 1.37/1.54      inference('sup+', [status(thm)], ['35', '36'])).
% 1.37/1.54  thf('38', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.37/1.54      inference('cnf', [status(esa)], [t3_boole])).
% 1.37/1.54  thf('39', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B))),
% 1.37/1.54      inference('demod', [status(thm)], ['37', '38'])).
% 1.37/1.54  thf('40', plain,
% 1.37/1.54      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_D @ sk_A))),
% 1.37/1.54      inference('demod', [status(thm)], ['32', '39'])).
% 1.37/1.54  thf('41', plain, ((r1_tarski @ sk_D @ sk_A)),
% 1.37/1.54      inference('simplify', [status(thm)], ['40'])).
% 1.37/1.54  thf(t12_xboole_1, axiom,
% 1.37/1.54    (![A:$i,B:$i]:
% 1.37/1.54     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.37/1.54  thf('42', plain,
% 1.37/1.54      (![X8 : $i, X9 : $i]:
% 1.37/1.54         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 1.37/1.54      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.37/1.54  thf('43', plain, (((k2_xboole_0 @ sk_D @ sk_A) = (sk_A))),
% 1.37/1.54      inference('sup-', [status(thm)], ['41', '42'])).
% 1.37/1.54  thf('44', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.37/1.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.37/1.54  thf('45', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_A))),
% 1.37/1.54      inference('demod', [status(thm)], ['43', '44'])).
% 1.37/1.54  thf('46', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 1.37/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.54  thf('47', plain,
% 1.37/1.54      (![X2 : $i, X3 : $i]:
% 1.37/1.54         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.37/1.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.37/1.54  thf('48', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 1.37/1.54      inference('sup-', [status(thm)], ['46', '47'])).
% 1.37/1.54  thf('49', plain,
% 1.37/1.54      (![X20 : $i, X21 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))
% 1.37/1.54           = (k4_xboole_0 @ X20 @ X21))),
% 1.37/1.54      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.37/1.54  thf('50', plain,
% 1.37/1.54      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_A))),
% 1.37/1.54      inference('sup+', [status(thm)], ['48', '49'])).
% 1.37/1.54  thf('51', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.37/1.54      inference('cnf', [status(esa)], [t3_boole])).
% 1.37/1.54  thf('52', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 1.37/1.54      inference('demod', [status(thm)], ['50', '51'])).
% 1.37/1.54  thf('53', plain,
% 1.37/1.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 1.37/1.54           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 1.37/1.54      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.37/1.54  thf('54', plain,
% 1.37/1.54      (![X0 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ sk_C @ X0)
% 1.37/1.54           = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.37/1.54      inference('sup+', [status(thm)], ['52', '53'])).
% 1.37/1.54  thf('55', plain,
% 1.37/1.54      (((k4_xboole_0 @ sk_C @ sk_D) = (k4_xboole_0 @ sk_C @ sk_A))),
% 1.37/1.54      inference('sup+', [status(thm)], ['45', '54'])).
% 1.37/1.54  thf('56', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 1.37/1.54      inference('demod', [status(thm)], ['50', '51'])).
% 1.37/1.54  thf('57', plain, (((k4_xboole_0 @ sk_C @ sk_D) = (sk_C))),
% 1.37/1.54      inference('demod', [status(thm)], ['55', '56'])).
% 1.37/1.54  thf('58', plain,
% 1.37/1.54      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D) = (sk_C))),
% 1.37/1.54      inference('demod', [status(thm)], ['4', '57'])).
% 1.37/1.54  thf('59', plain,
% 1.37/1.54      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_D) = (sk_C))),
% 1.37/1.54      inference('demod', [status(thm)], ['4', '57'])).
% 1.37/1.54  thf('60', plain,
% 1.37/1.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 1.37/1.54           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 1.37/1.54      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.37/1.54  thf('61', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.37/1.54      inference('demod', [status(thm)], ['24', '25'])).
% 1.37/1.54  thf('62', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 1.37/1.54           = (k1_xboole_0))),
% 1.37/1.54      inference('sup+', [status(thm)], ['60', '61'])).
% 1.37/1.54  thf('63', plain,
% 1.37/1.54      (![X12 : $i, X13 : $i]:
% 1.37/1.54         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 1.37/1.54           = (k2_xboole_0 @ X12 @ X13))),
% 1.37/1.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.37/1.54  thf('64', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 1.37/1.54      inference('demod', [status(thm)], ['62', '63'])).
% 1.37/1.54  thf(t52_xboole_1, axiom,
% 1.37/1.54    (![A:$i,B:$i,C:$i]:
% 1.37/1.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.37/1.54       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 1.37/1.54  thf('65', plain,
% 1.37/1.54      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X31))
% 1.37/1.54           = (k2_xboole_0 @ (k4_xboole_0 @ X29 @ X30) @ 
% 1.37/1.54              (k3_xboole_0 @ X29 @ X31)))),
% 1.37/1.54      inference('cnf', [status(esa)], [t52_xboole_1])).
% 1.37/1.54  thf('66', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 1.37/1.54           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.37/1.54      inference('sup+', [status(thm)], ['64', '65'])).
% 1.37/1.54  thf('67', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.37/1.54      inference('sup+', [status(thm)], ['15', '16'])).
% 1.37/1.54  thf('68', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 1.37/1.54           = (k3_xboole_0 @ X1 @ X0))),
% 1.37/1.54      inference('demod', [status(thm)], ['66', '67'])).
% 1.37/1.54  thf('69', plain,
% 1.37/1.54      (((k4_xboole_0 @ sk_A @ sk_C) = (k3_xboole_0 @ sk_A @ sk_D))),
% 1.37/1.54      inference('sup+', [status(thm)], ['59', '68'])).
% 1.37/1.54  thf('70', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.37/1.54      inference('cnf', [status(esa)], [t3_boole])).
% 1.37/1.54  thf('71', plain,
% 1.37/1.54      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X31))
% 1.37/1.54           = (k2_xboole_0 @ (k4_xboole_0 @ X29 @ X30) @ 
% 1.37/1.54              (k3_xboole_0 @ X29 @ X31)))),
% 1.37/1.54      inference('cnf', [status(esa)], [t52_xboole_1])).
% 1.37/1.54  thf('72', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1))
% 1.37/1.54           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.37/1.54      inference('sup+', [status(thm)], ['70', '71'])).
% 1.37/1.54  thf('73', plain,
% 1.37/1.54      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.37/1.54      inference('demod', [status(thm)], ['21', '26'])).
% 1.37/1.54  thf('74', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.37/1.54      inference('cnf', [status(esa)], [t3_boole])).
% 1.37/1.54  thf('75', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]:
% 1.37/1.54         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.37/1.54      inference('demod', [status(thm)], ['72', '73', '74'])).
% 1.37/1.54  thf('76', plain,
% 1.37/1.54      (![X0 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ sk_C @ X0)
% 1.37/1.54           = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.37/1.54      inference('sup+', [status(thm)], ['52', '53'])).
% 1.37/1.54  thf('77', plain,
% 1.37/1.54      (![X0 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ X0))
% 1.37/1.54           = (k4_xboole_0 @ sk_C @ sk_A))),
% 1.37/1.54      inference('sup+', [status(thm)], ['75', '76'])).
% 1.37/1.54  thf('78', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 1.37/1.54      inference('demod', [status(thm)], ['50', '51'])).
% 1.37/1.54  thf('79', plain,
% 1.37/1.54      (![X0 : $i]: ((k4_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ X0)) = (sk_C))),
% 1.37/1.54      inference('demod', [status(thm)], ['77', '78'])).
% 1.37/1.54  thf('80', plain,
% 1.37/1.54      (![X20 : $i, X21 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))
% 1.37/1.54           = (k4_xboole_0 @ X20 @ X21))),
% 1.37/1.54      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.37/1.54  thf(t51_xboole_1, axiom,
% 1.37/1.54    (![A:$i,B:$i]:
% 1.37/1.54     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.37/1.54       ( A ) ))).
% 1.37/1.54  thf('81', plain,
% 1.37/1.54      (![X27 : $i, X28 : $i]:
% 1.37/1.54         ((k2_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ (k4_xboole_0 @ X27 @ X28))
% 1.37/1.54           = (X27))),
% 1.37/1.54      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.37/1.54  thf('82', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]:
% 1.37/1.54         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.37/1.54           (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 1.37/1.54      inference('sup+', [status(thm)], ['80', '81'])).
% 1.37/1.54  thf('83', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.37/1.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.37/1.54  thf('84', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]:
% 1.37/1.54         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 1.37/1.54           (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))) = (X1))),
% 1.37/1.54      inference('demod', [status(thm)], ['82', '83'])).
% 1.37/1.54  thf('85', plain,
% 1.37/1.54      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X31))
% 1.37/1.54           = (k2_xboole_0 @ (k4_xboole_0 @ X29 @ X30) @ 
% 1.37/1.54              (k3_xboole_0 @ X29 @ X31)))),
% 1.37/1.54      inference('cnf', [status(esa)], [t52_xboole_1])).
% 1.37/1.54  thf('86', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 1.37/1.54           = (X1))),
% 1.37/1.54      inference('demod', [status(thm)], ['84', '85'])).
% 1.37/1.54  thf('87', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 1.37/1.54      inference('sup+', [status(thm)], ['79', '86'])).
% 1.37/1.54  thf('88', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_D))),
% 1.37/1.54      inference('demod', [status(thm)], ['69', '87'])).
% 1.37/1.54  thf('89', plain,
% 1.37/1.54      (![X20 : $i, X21 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))
% 1.37/1.54           = (k4_xboole_0 @ X20 @ X21))),
% 1.37/1.54      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.37/1.54  thf('90', plain,
% 1.37/1.54      (((k4_xboole_0 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_D))),
% 1.37/1.54      inference('sup+', [status(thm)], ['88', '89'])).
% 1.37/1.54  thf('91', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.37/1.54      inference('demod', [status(thm)], ['24', '25'])).
% 1.37/1.54  thf('92', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_D))),
% 1.37/1.54      inference('demod', [status(thm)], ['90', '91'])).
% 1.37/1.54  thf('93', plain,
% 1.37/1.54      (![X12 : $i, X13 : $i]:
% 1.37/1.54         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 1.37/1.54           = (k2_xboole_0 @ X12 @ X13))),
% 1.37/1.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.37/1.54  thf('94', plain,
% 1.37/1.54      (((k2_xboole_0 @ sk_D @ k1_xboole_0) = (k2_xboole_0 @ sk_D @ sk_A))),
% 1.37/1.54      inference('sup+', [status(thm)], ['92', '93'])).
% 1.37/1.54  thf('95', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.37/1.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.37/1.54  thf('96', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.37/1.54      inference('sup+', [status(thm)], ['15', '16'])).
% 1.37/1.54  thf('97', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.37/1.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.37/1.54  thf('98', plain, (((sk_D) = (k2_xboole_0 @ sk_A @ sk_D))),
% 1.37/1.54      inference('demod', [status(thm)], ['94', '95', '96', '97'])).
% 1.37/1.54  thf('99', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_A))),
% 1.37/1.54      inference('demod', [status(thm)], ['43', '44'])).
% 1.37/1.54  thf('100', plain, (((sk_D) = (sk_A))),
% 1.37/1.54      inference('sup+', [status(thm)], ['98', '99'])).
% 1.37/1.54  thf('101', plain,
% 1.37/1.54      (![X15 : $i, X16 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 1.37/1.54           = (k4_xboole_0 @ X15 @ X16))),
% 1.37/1.54      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.37/1.54  thf('102', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_C))),
% 1.37/1.54      inference('demod', [status(thm)], ['58', '100', '101'])).
% 1.37/1.54  thf('103', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]:
% 1.37/1.54         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.37/1.54      inference('demod', [status(thm)], ['72', '73', '74'])).
% 1.37/1.54  thf('104', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B))),
% 1.37/1.54      inference('demod', [status(thm)], ['37', '38'])).
% 1.37/1.54  thf('105', plain,
% 1.37/1.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 1.37/1.54           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 1.37/1.54      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.37/1.54  thf('106', plain,
% 1.37/1.54      (![X0 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ sk_D @ X0)
% 1.37/1.54           = (k4_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.37/1.54      inference('sup+', [status(thm)], ['104', '105'])).
% 1.37/1.54  thf('107', plain,
% 1.37/1.54      (![X0 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ sk_D @ (k3_xboole_0 @ sk_B @ X0))
% 1.37/1.54           = (k4_xboole_0 @ sk_D @ sk_B))),
% 1.37/1.54      inference('sup+', [status(thm)], ['103', '106'])).
% 1.37/1.54  thf('108', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B))),
% 1.37/1.54      inference('demod', [status(thm)], ['37', '38'])).
% 1.37/1.54  thf('109', plain,
% 1.37/1.54      (![X0 : $i]: ((k4_xboole_0 @ sk_D @ (k3_xboole_0 @ sk_B @ X0)) = (sk_D))),
% 1.37/1.54      inference('demod', [status(thm)], ['107', '108'])).
% 1.37/1.54  thf('110', plain,
% 1.37/1.54      (![X0 : $i, X1 : $i]:
% 1.37/1.54         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 1.37/1.54           = (X1))),
% 1.37/1.54      inference('demod', [status(thm)], ['84', '85'])).
% 1.37/1.54  thf('111', plain, (((k4_xboole_0 @ sk_B @ sk_D) = (sk_B))),
% 1.37/1.54      inference('sup+', [status(thm)], ['109', '110'])).
% 1.37/1.54  thf('112', plain, (((sk_D) = (sk_A))),
% 1.37/1.54      inference('sup+', [status(thm)], ['98', '99'])).
% 1.37/1.54  thf('113', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 1.37/1.54      inference('demod', [status(thm)], ['111', '112'])).
% 1.37/1.54  thf('114', plain, (((sk_C) = (sk_B))),
% 1.37/1.54      inference('sup+', [status(thm)], ['102', '113'])).
% 1.37/1.54  thf('115', plain, (((sk_C) != (sk_B))),
% 1.37/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.54  thf('116', plain, ($false),
% 1.37/1.54      inference('simplify_reflect-', [status(thm)], ['114', '115'])).
% 1.37/1.54  
% 1.37/1.54  % SZS output end Refutation
% 1.37/1.54  
% 1.37/1.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
