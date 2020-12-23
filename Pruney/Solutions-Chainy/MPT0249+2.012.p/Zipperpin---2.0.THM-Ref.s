%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OI9ZvDvEI3

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:40 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  147 (2262 expanded)
%              Number of leaves         :   25 ( 752 expanded)
%              Depth                    :   31
%              Number of atoms          : 1023 (17467 expanded)
%              Number of equality atoms :  155 (2439 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('6',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X49: $i,X50: $i] :
      ( ( X50
        = ( k1_tarski @ X49 ) )
      | ( X50 = k1_xboole_0 )
      | ~ ( r1_tarski @ X50 @ ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,
    ( sk_B
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['3','12'])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k2_xboole_0 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('15',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k3_tarski @ ( k2_tarski @ X8 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['0','17'])).

thf('19',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X49: $i,X50: $i] :
      ( ( X50
        = ( k1_tarski @ X49 ) )
      | ( X50 = k1_xboole_0 )
      | ~ ( r1_tarski @ X50 @ ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ sk_B )
        = sk_B )
      | ( ( k3_xboole_0 @ X0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ sk_B )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( ( k3_xboole_0 @ X0 @ sk_B )
        = sk_B ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ sk_B )
        = X0 )
      | ( ( k3_xboole_0 @ X0 @ sk_B )
        = sk_B ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
        = sk_B )
      | ( ( k4_xboole_0 @ X0 @ sk_B )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_B
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['3','12'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ sk_B )
        = sk_B )
      | ( ( k3_xboole_0 @ X0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
      | ( ( k3_xboole_0 @ X0 @ sk_B )
        = sk_B ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B )
      | ( ( k3_xboole_0 @ X0 @ sk_B )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ sk_B )
        = ( k5_xboole_0 @ X0 @ sk_B ) )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('41',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('42',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) )
      = X6 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('45',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('46',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X4 @ ( k3_tarski @ ( k2_tarski @ X4 @ X5 ) ) )
      = X4 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('50',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X4 @ ( k3_tarski @ ( k2_tarski @ X4 @ X5 ) ) )
      = X4 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('53',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) )
      = X6 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('56',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('57',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_tarski @ ( k2_tarski @ X11 @ X12 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['51','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('63',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('67',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['60','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['51','58'])).

thf('72',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['60','69'])).

thf('74',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['60','69'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['59','78'])).

thf('80',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_B ) )
        = X0 )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference('sup+',[status(thm)],['40','81'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('83',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('84',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('85',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) )
        = X0 )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['82','85'])).

thf('87',plain,
    ( ( sk_B = sk_C )
    | ( ( k4_xboole_0 @ sk_B @ sk_C )
      = sk_B ) ),
    inference('sup+',[status(thm)],['31','86'])).

thf('88',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('91',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_C @ sk_B ) )
    = ( k5_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_C @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ sk_B )
        = sk_B )
      | ( ( k3_xboole_0 @ X0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ sk_B )
        = sk_B ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) )
      = X6 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X0 @ sk_B ) )
        = X0 )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_C )
      = sk_C )
    | ( ( k3_xboole_0 @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['95','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('103',plain,
    ( ( ( k5_xboole_0 @ sk_C @ sk_C )
      = sk_B )
    | ( ( k3_xboole_0 @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('105',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( ( k3_xboole_0 @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_C @ sk_B )
      = sk_C ) ),
    inference('sup+',[status(thm)],['30','107'])).

thf('109',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = sk_C ),
    inference('simplify_reflect-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X19 @ X20 ) )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('112',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,
    ( sk_B
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['3','12'])).

thf('114',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('116',plain,
    ( sk_C
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('118',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['118','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OI9ZvDvEI3
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:49:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.69/0.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.92  % Solved by: fo/fo7.sh
% 0.69/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.92  % done 1285 iterations in 0.472s
% 0.69/0.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.92  % SZS output start Refutation
% 0.69/0.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.69/0.92  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.69/0.92  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.92  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.69/0.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.69/0.92  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.69/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.92  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.69/0.92  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.69/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.92  thf(commutativity_k3_xboole_0, axiom,
% 0.69/0.92    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.69/0.92  thf('0', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.69/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.69/0.92  thf(t44_zfmisc_1, conjecture,
% 0.69/0.92    (![A:$i,B:$i,C:$i]:
% 0.69/0.92     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.69/0.92          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.69/0.92          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.69/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.92    (~( ![A:$i,B:$i,C:$i]:
% 0.69/0.92        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.69/0.92             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.69/0.92             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.69/0.92    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.69/0.92  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf(l51_zfmisc_1, axiom,
% 0.69/0.92    (![A:$i,B:$i]:
% 0.69/0.92     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.69/0.92  thf('2', plain,
% 0.69/0.92      (![X52 : $i, X53 : $i]:
% 0.69/0.92         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 0.69/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.69/0.92  thf('3', plain,
% 0.69/0.92      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C)))),
% 0.69/0.92      inference('demod', [status(thm)], ['1', '2'])).
% 0.69/0.92  thf('4', plain,
% 0.69/0.92      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C)))),
% 0.69/0.92      inference('demod', [status(thm)], ['1', '2'])).
% 0.69/0.92  thf(t7_xboole_1, axiom,
% 0.69/0.92    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.69/0.92  thf('5', plain,
% 0.69/0.92      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.69/0.92      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.69/0.92  thf('6', plain,
% 0.69/0.92      (![X52 : $i, X53 : $i]:
% 0.69/0.92         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 0.69/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.69/0.92  thf('7', plain,
% 0.69/0.92      (![X14 : $i, X15 : $i]:
% 0.69/0.92         (r1_tarski @ X14 @ (k3_tarski @ (k2_tarski @ X14 @ X15)))),
% 0.69/0.92      inference('demod', [status(thm)], ['5', '6'])).
% 0.69/0.92  thf('8', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.69/0.92      inference('sup+', [status(thm)], ['4', '7'])).
% 0.69/0.92  thf(l3_zfmisc_1, axiom,
% 0.69/0.92    (![A:$i,B:$i]:
% 0.69/0.92     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.69/0.92       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.69/0.92  thf('9', plain,
% 0.69/0.92      (![X49 : $i, X50 : $i]:
% 0.69/0.92         (((X50) = (k1_tarski @ X49))
% 0.69/0.92          | ((X50) = (k1_xboole_0))
% 0.69/0.92          | ~ (r1_tarski @ X50 @ (k1_tarski @ X49)))),
% 0.69/0.92      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.69/0.92  thf('10', plain,
% 0.69/0.92      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['8', '9'])).
% 0.69/0.92  thf('11', plain, (((sk_B) != (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('12', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.69/0.92      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.69/0.92  thf('13', plain, (((sk_B) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C)))),
% 0.69/0.92      inference('demod', [status(thm)], ['3', '12'])).
% 0.69/0.92  thf(t29_xboole_1, axiom,
% 0.69/0.92    (![A:$i,B:$i,C:$i]:
% 0.69/0.92     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 0.69/0.92  thf('14', plain,
% 0.69/0.92      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.69/0.92         (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ (k2_xboole_0 @ X8 @ X10))),
% 0.69/0.92      inference('cnf', [status(esa)], [t29_xboole_1])).
% 0.69/0.92  thf('15', plain,
% 0.69/0.92      (![X52 : $i, X53 : $i]:
% 0.69/0.92         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 0.69/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.69/0.92  thf('16', plain,
% 0.69/0.92      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.69/0.92         (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ 
% 0.69/0.92          (k3_tarski @ (k2_tarski @ X8 @ X10)))),
% 0.69/0.92      inference('demod', [status(thm)], ['14', '15'])).
% 0.69/0.92  thf('17', plain,
% 0.69/0.92      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)),
% 0.69/0.92      inference('sup+', [status(thm)], ['13', '16'])).
% 0.69/0.92  thf('18', plain,
% 0.69/0.92      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B)),
% 0.69/0.92      inference('sup+', [status(thm)], ['0', '17'])).
% 0.69/0.92  thf('19', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.69/0.92      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.69/0.92  thf('20', plain,
% 0.69/0.92      (![X49 : $i, X50 : $i]:
% 0.69/0.92         (((X50) = (k1_tarski @ X49))
% 0.69/0.92          | ((X50) = (k1_xboole_0))
% 0.69/0.92          | ~ (r1_tarski @ X50 @ (k1_tarski @ X49)))),
% 0.69/0.92      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.69/0.92  thf('21', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (~ (r1_tarski @ X0 @ sk_B)
% 0.69/0.92          | ((X0) = (k1_xboole_0))
% 0.69/0.92          | ((X0) = (k1_tarski @ sk_A)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['19', '20'])).
% 0.69/0.92  thf('22', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.69/0.92      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.69/0.92  thf('23', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (~ (r1_tarski @ X0 @ sk_B) | ((X0) = (k1_xboole_0)) | ((X0) = (sk_B)))),
% 0.69/0.92      inference('demod', [status(thm)], ['21', '22'])).
% 0.69/0.92  thf('24', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k3_xboole_0 @ X0 @ sk_B) = (sk_B))
% 0.69/0.92          | ((k3_xboole_0 @ X0 @ sk_B) = (k1_xboole_0)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['18', '23'])).
% 0.69/0.92  thf(t100_xboole_1, axiom,
% 0.69/0.92    (![A:$i,B:$i]:
% 0.69/0.92     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.69/0.92  thf('25', plain,
% 0.69/0.92      (![X2 : $i, X3 : $i]:
% 0.69/0.92         ((k4_xboole_0 @ X2 @ X3)
% 0.69/0.92           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.69/0.92  thf('26', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k4_xboole_0 @ X0 @ sk_B) = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.69/0.92          | ((k3_xboole_0 @ X0 @ sk_B) = (sk_B)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['24', '25'])).
% 0.69/0.92  thf(t5_boole, axiom,
% 0.69/0.92    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.69/0.92  thf('27', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.69/0.92      inference('cnf', [status(esa)], [t5_boole])).
% 0.69/0.92  thf('28', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k4_xboole_0 @ X0 @ sk_B) = (X0))
% 0.69/0.92          | ((k3_xboole_0 @ X0 @ sk_B) = (sk_B)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['26', '27'])).
% 0.69/0.92  thf('29', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.69/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.69/0.92  thf('30', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k3_xboole_0 @ sk_B @ X0) = (sk_B))
% 0.69/0.92          | ((k4_xboole_0 @ X0 @ sk_B) = (X0)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['28', '29'])).
% 0.69/0.92  thf('31', plain, (((sk_B) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C)))),
% 0.69/0.92      inference('demod', [status(thm)], ['3', '12'])).
% 0.69/0.92  thf('32', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k3_xboole_0 @ X0 @ sk_B) = (sk_B))
% 0.69/0.92          | ((k3_xboole_0 @ X0 @ sk_B) = (k1_xboole_0)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['18', '23'])).
% 0.69/0.92  thf('33', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.69/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.69/0.92  thf('34', plain,
% 0.69/0.92      (![X2 : $i, X3 : $i]:
% 0.69/0.92         ((k4_xboole_0 @ X2 @ X3)
% 0.69/0.92           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.69/0.92  thf('35', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         ((k4_xboole_0 @ X0 @ X1)
% 0.69/0.92           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['33', '34'])).
% 0.69/0.92  thf('36', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k4_xboole_0 @ sk_B @ X0) = (k5_xboole_0 @ sk_B @ k1_xboole_0))
% 0.69/0.92          | ((k3_xboole_0 @ X0 @ sk_B) = (sk_B)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['32', '35'])).
% 0.69/0.92  thf('37', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.69/0.92      inference('cnf', [status(esa)], [t5_boole])).
% 0.69/0.92  thf('38', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k4_xboole_0 @ sk_B @ X0) = (sk_B))
% 0.69/0.92          | ((k3_xboole_0 @ X0 @ sk_B) = (sk_B)))),
% 0.69/0.92      inference('demod', [status(thm)], ['36', '37'])).
% 0.69/0.92  thf('39', plain,
% 0.69/0.92      (![X2 : $i, X3 : $i]:
% 0.69/0.92         ((k4_xboole_0 @ X2 @ X3)
% 0.69/0.92           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.69/0.92  thf('40', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k4_xboole_0 @ X0 @ sk_B) = (k5_xboole_0 @ X0 @ sk_B))
% 0.69/0.92          | ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['38', '39'])).
% 0.69/0.92  thf(t22_xboole_1, axiom,
% 0.69/0.92    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.69/0.92  thf('41', plain,
% 0.69/0.92      (![X6 : $i, X7 : $i]:
% 0.69/0.92         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)) = (X6))),
% 0.69/0.92      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.69/0.92  thf('42', plain,
% 0.69/0.92      (![X52 : $i, X53 : $i]:
% 0.69/0.92         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 0.69/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.69/0.92  thf('43', plain,
% 0.69/0.92      (![X6 : $i, X7 : $i]:
% 0.69/0.92         ((k3_tarski @ (k2_tarski @ X6 @ (k3_xboole_0 @ X6 @ X7))) = (X6))),
% 0.69/0.92      inference('demod', [status(thm)], ['41', '42'])).
% 0.69/0.92  thf(t21_xboole_1, axiom,
% 0.69/0.92    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.69/0.92  thf('44', plain,
% 0.69/0.92      (![X4 : $i, X5 : $i]:
% 0.69/0.92         ((k3_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (X4))),
% 0.69/0.92      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.69/0.92  thf('45', plain,
% 0.69/0.92      (![X52 : $i, X53 : $i]:
% 0.69/0.92         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 0.69/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.69/0.92  thf('46', plain,
% 0.69/0.92      (![X4 : $i, X5 : $i]:
% 0.69/0.92         ((k3_xboole_0 @ X4 @ (k3_tarski @ (k2_tarski @ X4 @ X5))) = (X4))),
% 0.69/0.92      inference('demod', [status(thm)], ['44', '45'])).
% 0.69/0.92  thf('47', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.69/0.92      inference('sup+', [status(thm)], ['43', '46'])).
% 0.69/0.92  thf('48', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         ((k4_xboole_0 @ X0 @ X1)
% 0.69/0.92           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['33', '34'])).
% 0.69/0.92  thf('49', plain,
% 0.69/0.92      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.69/0.92      inference('sup+', [status(thm)], ['47', '48'])).
% 0.69/0.92  thf(t91_xboole_1, axiom,
% 0.69/0.92    (![A:$i,B:$i,C:$i]:
% 0.69/0.92     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.69/0.92       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.69/0.92  thf('50', plain,
% 0.69/0.92      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.69/0.92         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.69/0.92           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.69/0.92  thf('51', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.69/0.92           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.69/0.92      inference('sup+', [status(thm)], ['49', '50'])).
% 0.69/0.92  thf('52', plain,
% 0.69/0.92      (![X4 : $i, X5 : $i]:
% 0.69/0.92         ((k3_xboole_0 @ X4 @ (k3_tarski @ (k2_tarski @ X4 @ X5))) = (X4))),
% 0.69/0.92      inference('demod', [status(thm)], ['44', '45'])).
% 0.69/0.92  thf('53', plain,
% 0.69/0.92      (![X6 : $i, X7 : $i]:
% 0.69/0.92         ((k3_tarski @ (k2_tarski @ X6 @ (k3_xboole_0 @ X6 @ X7))) = (X6))),
% 0.69/0.92      inference('demod', [status(thm)], ['41', '42'])).
% 0.69/0.92  thf('54', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.69/0.92      inference('sup+', [status(thm)], ['52', '53'])).
% 0.69/0.92  thf(t46_xboole_1, axiom,
% 0.69/0.92    (![A:$i,B:$i]:
% 0.69/0.92     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.69/0.92  thf('55', plain,
% 0.69/0.92      (![X11 : $i, X12 : $i]:
% 0.69/0.92         ((k4_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.69/0.92  thf('56', plain,
% 0.69/0.92      (![X52 : $i, X53 : $i]:
% 0.69/0.92         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 0.69/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.69/0.92  thf('57', plain,
% 0.69/0.92      (![X11 : $i, X12 : $i]:
% 0.69/0.92         ((k4_xboole_0 @ X11 @ (k3_tarski @ (k2_tarski @ X11 @ X12)))
% 0.69/0.92           = (k1_xboole_0))),
% 0.69/0.92      inference('demod', [status(thm)], ['55', '56'])).
% 0.69/0.92  thf('58', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.69/0.92      inference('sup+', [status(thm)], ['54', '57'])).
% 0.69/0.92  thf('59', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         ((k1_xboole_0)
% 0.69/0.92           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.69/0.92      inference('demod', [status(thm)], ['51', '58'])).
% 0.69/0.92  thf('60', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.69/0.92      inference('sup+', [status(thm)], ['54', '57'])).
% 0.69/0.92  thf('61', plain,
% 0.69/0.92      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.69/0.92      inference('sup+', [status(thm)], ['47', '48'])).
% 0.69/0.92  thf('62', plain,
% 0.69/0.92      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.69/0.92      inference('sup+', [status(thm)], ['47', '48'])).
% 0.69/0.92  thf('63', plain,
% 0.69/0.92      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.69/0.92         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.69/0.92           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.69/0.92  thf('64', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.69/0.92           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['62', '63'])).
% 0.69/0.92  thf('65', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 0.69/0.92           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['61', '64'])).
% 0.69/0.92  thf('66', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.69/0.92      inference('sup+', [status(thm)], ['54', '57'])).
% 0.69/0.92  thf('67', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.69/0.92      inference('cnf', [status(esa)], [t5_boole])).
% 0.69/0.92  thf('68', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.69/0.92      inference('sup+', [status(thm)], ['66', '67'])).
% 0.69/0.92  thf('69', plain,
% 0.69/0.92      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.69/0.92      inference('demod', [status(thm)], ['65', '68'])).
% 0.69/0.92  thf('70', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.69/0.92      inference('sup+', [status(thm)], ['60', '69'])).
% 0.69/0.92  thf('71', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         ((k1_xboole_0)
% 0.69/0.92           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.69/0.92      inference('demod', [status(thm)], ['51', '58'])).
% 0.69/0.92  thf('72', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['70', '71'])).
% 0.69/0.92  thf('73', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.69/0.92      inference('sup+', [status(thm)], ['60', '69'])).
% 0.69/0.92  thf('74', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.69/0.92      inference('demod', [status(thm)], ['72', '73'])).
% 0.69/0.92  thf('75', plain,
% 0.69/0.92      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.69/0.92         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.69/0.92           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.69/0.92  thf('76', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.69/0.92           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['74', '75'])).
% 0.69/0.92  thf('77', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.69/0.92      inference('sup+', [status(thm)], ['60', '69'])).
% 0.69/0.92  thf('78', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.69/0.92      inference('demod', [status(thm)], ['76', '77'])).
% 0.69/0.92  thf('79', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.69/0.92           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.69/0.92      inference('sup+', [status(thm)], ['59', '78'])).
% 0.69/0.92  thf('80', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.69/0.92      inference('cnf', [status(esa)], [t5_boole])).
% 0.69/0.92  thf('81', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.69/0.92      inference('demod', [status(thm)], ['79', '80'])).
% 0.69/0.92  thf('82', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k5_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_B)) = (X0))
% 0.69/0.92          | ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['40', '81'])).
% 0.69/0.92  thf(t98_xboole_1, axiom,
% 0.69/0.92    (![A:$i,B:$i]:
% 0.69/0.92     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.69/0.92  thf('83', plain,
% 0.69/0.92      (![X19 : $i, X20 : $i]:
% 0.69/0.92         ((k2_xboole_0 @ X19 @ X20)
% 0.69/0.92           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.69/0.92  thf('84', plain,
% 0.69/0.92      (![X52 : $i, X53 : $i]:
% 0.69/0.92         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 0.69/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.69/0.92  thf('85', plain,
% 0.69/0.92      (![X19 : $i, X20 : $i]:
% 0.69/0.92         ((k3_tarski @ (k2_tarski @ X19 @ X20))
% 0.69/0.92           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.69/0.92      inference('demod', [status(thm)], ['83', '84'])).
% 0.69/0.92  thf('86', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k3_tarski @ (k2_tarski @ sk_B @ X0)) = (X0))
% 0.69/0.92          | ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 0.69/0.92      inference('demod', [status(thm)], ['82', '85'])).
% 0.69/0.92  thf('87', plain,
% 0.69/0.92      ((((sk_B) = (sk_C)) | ((k4_xboole_0 @ sk_B @ sk_C) = (sk_B)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['31', '86'])).
% 0.69/0.92  thf('88', plain, (((sk_B) != (sk_C))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('89', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 0.69/0.92      inference('simplify_reflect-', [status(thm)], ['87', '88'])).
% 0.69/0.92  thf('90', plain,
% 0.69/0.92      (![X19 : $i, X20 : $i]:
% 0.69/0.92         ((k3_tarski @ (k2_tarski @ X19 @ X20))
% 0.69/0.92           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.69/0.92      inference('demod', [status(thm)], ['83', '84'])).
% 0.69/0.92  thf('91', plain,
% 0.69/0.92      (((k3_tarski @ (k2_tarski @ sk_C @ sk_B)) = (k5_xboole_0 @ sk_C @ sk_B))),
% 0.69/0.92      inference('sup+', [status(thm)], ['89', '90'])).
% 0.69/0.92  thf('92', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.69/0.92      inference('demod', [status(thm)], ['79', '80'])).
% 0.69/0.92  thf('93', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.69/0.92      inference('demod', [status(thm)], ['76', '77'])).
% 0.69/0.92  thf('94', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.69/0.92      inference('sup+', [status(thm)], ['92', '93'])).
% 0.69/0.92  thf('95', plain,
% 0.69/0.92      (((k3_tarski @ (k2_tarski @ sk_C @ sk_B)) = (k5_xboole_0 @ sk_B @ sk_C))),
% 0.69/0.92      inference('demod', [status(thm)], ['91', '94'])).
% 0.69/0.92  thf('96', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k3_xboole_0 @ X0 @ sk_B) = (sk_B))
% 0.69/0.92          | ((k3_xboole_0 @ X0 @ sk_B) = (k1_xboole_0)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['18', '23'])).
% 0.69/0.92  thf('97', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.69/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.69/0.92  thf('98', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k3_xboole_0 @ sk_B @ X0) = (k1_xboole_0))
% 0.69/0.92          | ((k3_xboole_0 @ X0 @ sk_B) = (sk_B)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['96', '97'])).
% 0.69/0.92  thf('99', plain,
% 0.69/0.92      (![X6 : $i, X7 : $i]:
% 0.69/0.92         ((k3_tarski @ (k2_tarski @ X6 @ (k3_xboole_0 @ X6 @ X7))) = (X6))),
% 0.69/0.92      inference('demod', [status(thm)], ['41', '42'])).
% 0.69/0.92  thf('100', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k3_tarski @ (k2_tarski @ X0 @ sk_B)) = (X0))
% 0.69/0.92          | ((k3_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['98', '99'])).
% 0.69/0.92  thf('101', plain,
% 0.69/0.92      ((((k5_xboole_0 @ sk_B @ sk_C) = (sk_C))
% 0.69/0.92        | ((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['95', '100'])).
% 0.69/0.92  thf('102', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.69/0.92      inference('demod', [status(thm)], ['79', '80'])).
% 0.69/0.92  thf('103', plain,
% 0.69/0.92      ((((k5_xboole_0 @ sk_C @ sk_C) = (sk_B))
% 0.69/0.92        | ((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['101', '102'])).
% 0.69/0.92  thf('104', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.69/0.92      inference('demod', [status(thm)], ['72', '73'])).
% 0.69/0.92  thf('105', plain,
% 0.69/0.92      ((((k1_xboole_0) = (sk_B))
% 0.69/0.92        | ((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.69/0.92      inference('demod', [status(thm)], ['103', '104'])).
% 0.69/0.92  thf('106', plain, (((sk_B) != (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('107', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.69/0.92      inference('simplify_reflect-', [status(thm)], ['105', '106'])).
% 0.69/0.92  thf('108', plain,
% 0.69/0.92      ((((sk_B) = (k1_xboole_0)) | ((k4_xboole_0 @ sk_C @ sk_B) = (sk_C)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['30', '107'])).
% 0.69/0.92  thf('109', plain, (((sk_B) != (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('110', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (sk_C))),
% 0.69/0.92      inference('simplify_reflect-', [status(thm)], ['108', '109'])).
% 0.69/0.92  thf('111', plain,
% 0.69/0.92      (![X19 : $i, X20 : $i]:
% 0.69/0.92         ((k3_tarski @ (k2_tarski @ X19 @ X20))
% 0.69/0.92           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.69/0.92      inference('demod', [status(thm)], ['83', '84'])).
% 0.69/0.92  thf('112', plain,
% 0.69/0.92      (((k3_tarski @ (k2_tarski @ sk_B @ sk_C)) = (k5_xboole_0 @ sk_B @ sk_C))),
% 0.69/0.92      inference('sup+', [status(thm)], ['110', '111'])).
% 0.69/0.92  thf('113', plain, (((sk_B) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C)))),
% 0.69/0.92      inference('demod', [status(thm)], ['3', '12'])).
% 0.69/0.92  thf('114', plain, (((sk_B) = (k5_xboole_0 @ sk_B @ sk_C))),
% 0.69/0.92      inference('sup+', [status(thm)], ['112', '113'])).
% 0.69/0.92  thf('115', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.69/0.92      inference('demod', [status(thm)], ['76', '77'])).
% 0.69/0.92  thf('116', plain, (((sk_C) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.69/0.92      inference('sup+', [status(thm)], ['114', '115'])).
% 0.69/0.92  thf('117', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.69/0.92      inference('demod', [status(thm)], ['72', '73'])).
% 0.69/0.92  thf('118', plain, (((sk_C) = (k1_xboole_0))),
% 0.69/0.92      inference('demod', [status(thm)], ['116', '117'])).
% 0.69/0.92  thf('119', plain, (((sk_C) != (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('120', plain, ($false),
% 0.69/0.92      inference('simplify_reflect-', [status(thm)], ['118', '119'])).
% 0.69/0.92  
% 0.69/0.92  % SZS output end Refutation
% 0.69/0.92  
% 0.69/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
