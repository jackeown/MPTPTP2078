%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UWmcGtC1an

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:56 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 455 expanded)
%              Number of leaves         :   30 ( 156 expanded)
%              Depth                    :   22
%              Number of atoms          :  667 (2970 expanded)
%              Number of equality atoms :   91 ( 341 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('7',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( r2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(antisymmetry_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
     => ~ ( r2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_xboole_0])).

thf('9',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( r2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['10'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X67: $i,X68: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X67 @ X68 ) )
      = ( k2_xboole_0 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('14',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('15',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('16',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    r1_tarski @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('20',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( r2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['20','23'])).

thf('25',plain,
    ( k1_xboole_0
    = ( k2_tarski @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','24'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('27',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['20','23'])).

thf('35',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['20','23'])).

thf('36',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
    = ( k5_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k5_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) @ sk_B )
    = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','38'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('40',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('43',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('44',plain,
    ( ( k5_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['39','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('46',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('49',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['20','23'])).

thf('50',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_B )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_B )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('57',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ sk_B )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
    = ( k5_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('61',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('63',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60','61','64'])).

thf('66',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('69',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('70',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','65','71'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('73',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('74',plain,
    ( k1_xboole_0
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','72','73'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('75',plain,(
    ! [X69: $i,X70: $i] :
      ( ( X70 != X69 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X70 ) @ ( k1_tarski @ X69 ) )
       != ( k1_tarski @ X70 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('76',plain,(
    ! [X69: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X69 ) @ ( k1_tarski @ X69 ) )
     != ( k1_tarski @ X69 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('78',plain,(
    ! [X69: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X69 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','78'])).

thf('80',plain,(
    $false ),
    inference(simplify,[status(thm)],['79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UWmcGtC1an
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:03:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 250 iterations in 0.100s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.37/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.55  thf('0', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.37/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.55  thf(d8_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.37/0.55       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (![X2 : $i, X4 : $i]:
% 0.37/0.55         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.37/0.55      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.55  thf(t50_zfmisc_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.55        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t7_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.37/0.55  thf('5', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0)),
% 0.37/0.55      inference('sup+', [status(thm)], ['3', '4'])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (![X2 : $i, X4 : $i]:
% 0.37/0.55         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.37/0.55      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.37/0.55        | (r2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.55  thf(antisymmetry_r2_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ( r2_xboole_0 @ A @ B ) => ( ~( r2_xboole_0 @ B @ A ) ) ))).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (r2_xboole_0 @ X0 @ X1) | ~ (r2_xboole_0 @ X1 @ X0))),
% 0.37/0.55      inference('cnf', [status(esa)], [antisymmetry_r2_xboole_0])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.37/0.55        | ~ (r2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      ((((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))
% 0.37/0.55        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['2', '9'])).
% 0.37/0.55  thf('11', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))),
% 0.37/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.37/0.55  thf('12', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))),
% 0.37/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.37/0.55  thf(l51_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (![X67 : $i, X68 : $i]:
% 0.37/0.55         ((k3_tarski @ (k2_tarski @ X67 @ X68)) = (k2_xboole_0 @ X67 @ X68))),
% 0.37/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.55  thf('14', plain, (((k3_tarski @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.55      inference('sup+', [status(thm)], ['12', '13'])).
% 0.37/0.55  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.37/0.55  thf('15', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.37/0.55  thf('16', plain, (((k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.37/0.55  thf('18', plain, ((r1_tarski @ sk_A @ k1_xboole_0)),
% 0.37/0.55      inference('sup+', [status(thm)], ['16', '17'])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (![X2 : $i, X4 : $i]:
% 0.37/0.55         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.37/0.55      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      ((((sk_A) = (k1_xboole_0)) | (r2_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (r2_xboole_0 @ X0 @ X1) | ~ (r2_xboole_0 @ X1 @ X0))),
% 0.37/0.55      inference('cnf', [status(esa)], [antisymmetry_r2_xboole_0])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k1_xboole_0) = (X0)) | ~ (r2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf('24', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.55      inference('clc', [status(thm)], ['20', '23'])).
% 0.37/0.55  thf('25', plain, (((k1_xboole_0) = (k2_tarski @ k1_xboole_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['11', '24'])).
% 0.37/0.55  thf(t92_xboole_1, axiom,
% 0.37/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.55  thf('26', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.55  thf('27', plain, (((k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.55  thf(t95_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k3_xboole_0 @ A @ B ) =
% 0.37/0.55       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      (![X18 : $i, X19 : $i]:
% 0.37/0.55         ((k3_xboole_0 @ X18 @ X19)
% 0.37/0.55           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 0.37/0.55              (k2_xboole_0 @ X18 @ X19)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.37/0.55  thf(t91_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.55       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.37/0.55           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      (![X18 : $i, X19 : $i]:
% 0.37/0.55         ((k3_xboole_0 @ X18 @ X19)
% 0.37/0.55           = (k5_xboole_0 @ X18 @ 
% 0.37/0.55              (k5_xboole_0 @ X19 @ (k2_xboole_0 @ X18 @ X19))))),
% 0.37/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.37/0.55         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ k1_xboole_0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['27', '30'])).
% 0.37/0.55  thf(t5_boole, axiom,
% 0.37/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.55  thf('32', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.37/0.55      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      (((k3_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['31', '32'])).
% 0.37/0.55  thf('34', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.55      inference('clc', [status(thm)], ['20', '23'])).
% 0.37/0.55  thf('35', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.55      inference('clc', [status(thm)], ['20', '23'])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      (((k3_xboole_0 @ k1_xboole_0 @ sk_B) = (k5_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.37/0.55  thf('37', plain,
% 0.37/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.37/0.55           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.55  thf('38', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ sk_B) @ X0)
% 0.37/0.55           = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ sk_B @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['36', '37'])).
% 0.37/0.55  thf('39', plain,
% 0.37/0.55      (((k5_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ sk_B) @ sk_B)
% 0.37/0.55         = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['26', '38'])).
% 0.37/0.55  thf(idempotence_k3_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.55  thf('40', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.55  thf(t100_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      (![X7 : $i, X8 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ X7 @ X8)
% 0.37/0.55           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.55  thf('42', plain,
% 0.37/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['40', '41'])).
% 0.37/0.55  thf(t4_boole, axiom,
% 0.37/0.55    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.55  thf('43', plain,
% 0.37/0.55      (![X10 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t4_boole])).
% 0.37/0.55  thf('44', plain,
% 0.37/0.55      (((k5_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ sk_B) @ sk_B)
% 0.37/0.55         = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['39', '42', '43'])).
% 0.37/0.55  thf('45', plain,
% 0.37/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['40', '41'])).
% 0.37/0.55  thf('46', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.55  thf('47', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['45', '46'])).
% 0.37/0.55  thf('48', plain, (((k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.55  thf('49', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.55      inference('clc', [status(thm)], ['20', '23'])).
% 0.37/0.55  thf('50', plain, (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['48', '49'])).
% 0.37/0.55  thf('51', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k1_xboole_0) = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ sk_B))),
% 0.37/0.55      inference('sup+', [status(thm)], ['47', '50'])).
% 0.37/0.55  thf('52', plain,
% 0.37/0.55      (![X18 : $i, X19 : $i]:
% 0.37/0.55         ((k3_xboole_0 @ X18 @ X19)
% 0.37/0.55           = (k5_xboole_0 @ X18 @ 
% 0.37/0.55              (k5_xboole_0 @ X19 @ (k2_xboole_0 @ X18 @ X19))))),
% 0.37/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.55  thf('53', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ sk_B)
% 0.37/0.55           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 0.37/0.55              (k5_xboole_0 @ sk_B @ k1_xboole_0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['51', '52'])).
% 0.37/0.55  thf('54', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.37/0.55      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.55  thf('55', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ sk_B)
% 0.37/0.55           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['53', '54'])).
% 0.37/0.55  thf('56', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.55  thf('57', plain,
% 0.37/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.37/0.55           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.55  thf('58', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.55           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['56', '57'])).
% 0.37/0.55  thf('59', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ k1_xboole_0 @ sk_B)
% 0.37/0.55           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 0.37/0.55              (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ sk_B)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['55', '58'])).
% 0.37/0.55  thf('60', plain,
% 0.37/0.55      (((k3_xboole_0 @ k1_xboole_0 @ sk_B) = (k5_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.37/0.55  thf('61', plain,
% 0.37/0.55      (![X7 : $i, X8 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ X7 @ X8)
% 0.37/0.55           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.55  thf('62', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['45', '46'])).
% 0.37/0.55  thf('63', plain,
% 0.37/0.55      (![X10 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t4_boole])).
% 0.37/0.55  thf('64', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['62', '63'])).
% 0.37/0.55  thf('65', plain, (((k3_xboole_0 @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['59', '60', '61', '64'])).
% 0.37/0.55  thf('66', plain,
% 0.37/0.55      (![X18 : $i, X19 : $i]:
% 0.37/0.55         ((k3_xboole_0 @ X18 @ X19)
% 0.37/0.55           = (k5_xboole_0 @ X18 @ 
% 0.37/0.55              (k5_xboole_0 @ X19 @ (k2_xboole_0 @ X18 @ X19))))),
% 0.37/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.55  thf('67', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.55           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['56', '57'])).
% 0.37/0.55  thf('68', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0))
% 0.37/0.55           = (k3_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['66', '67'])).
% 0.37/0.55  thf(idempotence_k2_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.55  thf('69', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ X5) = (X5))),
% 0.37/0.55      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.37/0.55  thf('70', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.55  thf('71', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.37/0.55  thf('72', plain, (((sk_B) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['44', '65', '71'])).
% 0.37/0.55  thf(t69_enumset1, axiom,
% 0.37/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.55  thf('73', plain,
% 0.37/0.55      (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 0.37/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.55  thf('74', plain, (((k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['25', '72', '73'])).
% 0.37/0.55  thf(t20_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.55         ( k1_tarski @ A ) ) <=>
% 0.37/0.55       ( ( A ) != ( B ) ) ))).
% 0.37/0.55  thf('75', plain,
% 0.37/0.55      (![X69 : $i, X70 : $i]:
% 0.37/0.55         (((X70) != (X69))
% 0.37/0.55          | ((k4_xboole_0 @ (k1_tarski @ X70) @ (k1_tarski @ X69))
% 0.37/0.55              != (k1_tarski @ X70)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.37/0.55  thf('76', plain,
% 0.37/0.55      (![X69 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ (k1_tarski @ X69) @ (k1_tarski @ X69))
% 0.37/0.55           != (k1_tarski @ X69))),
% 0.37/0.55      inference('simplify', [status(thm)], ['75'])).
% 0.37/0.55  thf('77', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['45', '46'])).
% 0.37/0.55  thf('78', plain, (![X69 : $i]: ((k1_xboole_0) != (k1_tarski @ X69))),
% 0.37/0.55      inference('demod', [status(thm)], ['76', '77'])).
% 0.37/0.55  thf('79', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['74', '78'])).
% 0.37/0.55  thf('80', plain, ($false), inference('simplify', [status(thm)], ['79'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.39/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
