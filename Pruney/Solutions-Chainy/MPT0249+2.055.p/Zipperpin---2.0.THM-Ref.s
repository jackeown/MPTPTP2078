%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.joBhV6pqTf

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:46 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 408 expanded)
%              Number of leaves         :   20 ( 138 expanded)
%              Depth                    :   19
%              Number of atoms          :  612 (3408 expanded)
%              Number of equality atoms :   91 ( 546 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('4',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X43
        = ( k1_tarski @ X42 ) )
      | ( X43 = k1_xboole_0 )
      | ~ ( r1_tarski @ X43 @ ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('5',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('8',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','7'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_C @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('29',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','30'])).

thf('32',plain,
    ( sk_C
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','31'])).

thf('33',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','43'])).

thf('45',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['32','44'])).

thf('46',plain,
    ( sk_C
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','45'])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','30'])).

thf('49',plain,
    ( ( k5_xboole_0 @ sk_C @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,
    ( ( k5_xboole_0 @ sk_C @ sk_B )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( sk_C
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','51'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('53',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('54',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('55',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X43
        = ( k1_tarski @ X42 ) )
      | ( X43 = k1_xboole_0 )
      | ~ ( r1_tarski @ X43 @ ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,
    ( sk_C
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','51'])).

thf('61',plain,
    ( ( sk_C
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
    | ( ( k4_xboole_0 @ sk_B @ sk_C )
      = sk_B ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','43'])).

thf('63',plain,
    ( ( sk_C = sk_B )
    | ( ( k4_xboole_0 @ sk_B @ sk_C )
      = sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('68',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['52','65','66','67'])).

thf('69',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.joBhV6pqTf
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:12:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 200 iterations in 0.061s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(t44_zfmisc_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.37/0.55          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.55          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.55        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.37/0.55             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.55             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.37/0.55  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t7_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.37/0.55  thf('3', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.37/0.55      inference('sup+', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf(l3_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.37/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (![X42 : $i, X43 : $i]:
% 0.37/0.55         (((X43) = (k1_tarski @ X42))
% 0.37/0.55          | ((X43) = (k1_xboole_0))
% 0.37/0.55          | ~ (r1_tarski @ X43 @ (k1_tarski @ X42)))),
% 0.37/0.55      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.37/0.55  thf('5', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.55  thf('6', plain, (((sk_B) != (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('7', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.37/0.55  thf('8', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.37/0.55      inference('demod', [status(thm)], ['0', '7'])).
% 0.37/0.55  thf(t95_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k3_xboole_0 @ A @ B ) =
% 0.37/0.55       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i]:
% 0.37/0.55         ((k3_xboole_0 @ X12 @ X13)
% 0.37/0.55           = (k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ 
% 0.37/0.55              (k2_xboole_0 @ X12 @ X13)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.37/0.55  thf(t91_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.55       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.37/0.55           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i]:
% 0.37/0.55         ((k3_xboole_0 @ X12 @ X13)
% 0.37/0.55           = (k5_xboole_0 @ X12 @ 
% 0.37/0.55              (k5_xboole_0 @ X13 @ (k2_xboole_0 @ X12 @ X13))))),
% 0.37/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.37/0.55         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ sk_B)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['8', '11'])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.37/0.55           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.55  thf(t92_xboole_1, axiom,
% 0.37/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.55  thf('14', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.37/0.55           = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['13', '14'])).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.37/0.55         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ sk_B)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['8', '11'])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.37/0.55           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ X0)
% 0.37/0.55           = (k5_xboole_0 @ sk_B @ 
% 0.37/0.55              (k5_xboole_0 @ (k5_xboole_0 @ sk_C @ sk_B) @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['16', '17'])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.37/0.55           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ X0)
% 0.37/0.55           = (k5_xboole_0 @ sk_B @ 
% 0.37/0.55              (k5_xboole_0 @ sk_C @ (k5_xboole_0 @ sk_B @ X0))))),
% 0.37/0.55      inference('demod', [status(thm)], ['18', '19'])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      (((k5_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_C) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['15', '20'])).
% 0.37/0.55  thf('22', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.37/0.55           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.55           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['22', '23'])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i]:
% 0.37/0.55         ((k3_xboole_0 @ X12 @ X13)
% 0.37/0.55           = (k5_xboole_0 @ X12 @ 
% 0.37/0.55              (k5_xboole_0 @ X13 @ (k2_xboole_0 @ X12 @ X13))))),
% 0.37/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.55           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['22', '23'])).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0))
% 0.37/0.55           = (k3_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['25', '26'])).
% 0.37/0.55  thf(idempotence_k2_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.55  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.55      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.37/0.55  thf(idempotence_k3_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.55  thf('29', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 0.37/0.55      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.55  thf('30', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['24', '30'])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      (((sk_C) = (k5_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['21', '31'])).
% 0.37/0.55  thf('33', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 0.37/0.55      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.55  thf(t100_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (![X2 : $i, X3 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ X2 @ X3)
% 0.37/0.55           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['33', '34'])).
% 0.37/0.55  thf('36', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.55  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['35', '36'])).
% 0.37/0.55  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.55      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.37/0.55  thf('39', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i]:
% 0.37/0.55         ((k3_xboole_0 @ X12 @ X13)
% 0.37/0.55           = (k5_xboole_0 @ X12 @ 
% 0.37/0.55              (k5_xboole_0 @ X13 @ (k2_xboole_0 @ X12 @ X13))))),
% 0.37/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k3_xboole_0 @ X0 @ X0)
% 0.37/0.55           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['38', '39'])).
% 0.37/0.55  thf('41', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 0.37/0.55      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.55  thf('42', plain,
% 0.37/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['33', '34'])).
% 0.37/0.55  thf('43', plain,
% 0.37/0.55      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.37/0.55  thf('44', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['37', '43'])).
% 0.37/0.55  thf('45', plain, (((sk_C) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.37/0.55      inference('demod', [status(thm)], ['32', '44'])).
% 0.37/0.55  thf('46', plain,
% 0.37/0.55      (((sk_C) = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ sk_B)))),
% 0.37/0.55      inference('demod', [status(thm)], ['12', '45'])).
% 0.37/0.55  thf('47', plain,
% 0.37/0.55      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.37/0.55         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ sk_B)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['8', '11'])).
% 0.37/0.55  thf('48', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['24', '30'])).
% 0.37/0.55  thf('49', plain,
% 0.37/0.55      (((k5_xboole_0 @ sk_C @ sk_B)
% 0.37/0.55         = (k5_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['47', '48'])).
% 0.37/0.55  thf('50', plain,
% 0.37/0.55      (![X2 : $i, X3 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ X2 @ X3)
% 0.37/0.55           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.55  thf('51', plain,
% 0.37/0.55      (((k5_xboole_0 @ sk_C @ sk_B) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.37/0.55      inference('demod', [status(thm)], ['49', '50'])).
% 0.37/0.55  thf('52', plain,
% 0.37/0.55      (((sk_C) = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.37/0.55      inference('demod', [status(thm)], ['46', '51'])).
% 0.37/0.55  thf(t36_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.55  thf('53', plain,
% 0.37/0.55      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.37/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.37/0.55  thf('54', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.37/0.55  thf('55', plain,
% 0.37/0.55      (![X42 : $i, X43 : $i]:
% 0.37/0.55         (((X43) = (k1_tarski @ X42))
% 0.37/0.55          | ((X43) = (k1_xboole_0))
% 0.37/0.55          | ~ (r1_tarski @ X43 @ (k1_tarski @ X42)))),
% 0.37/0.55      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.37/0.55  thf('56', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r1_tarski @ X0 @ sk_B)
% 0.37/0.55          | ((X0) = (k1_xboole_0))
% 0.37/0.55          | ((X0) = (k1_tarski @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.37/0.55  thf('57', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.37/0.55  thf('58', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r1_tarski @ X0 @ sk_B) | ((X0) = (k1_xboole_0)) | ((X0) = (sk_B)))),
% 0.37/0.55      inference('demod', [status(thm)], ['56', '57'])).
% 0.37/0.55  thf('59', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k4_xboole_0 @ sk_B @ X0) = (sk_B))
% 0.37/0.55          | ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['53', '58'])).
% 0.37/0.55  thf('60', plain,
% 0.37/0.55      (((sk_C) = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.37/0.55      inference('demod', [status(thm)], ['46', '51'])).
% 0.37/0.55  thf('61', plain,
% 0.37/0.55      ((((sk_C) = (k5_xboole_0 @ sk_B @ k1_xboole_0))
% 0.37/0.55        | ((k4_xboole_0 @ sk_B @ sk_C) = (sk_B)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['59', '60'])).
% 0.37/0.55  thf('62', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['37', '43'])).
% 0.37/0.55  thf('63', plain,
% 0.37/0.55      ((((sk_C) = (sk_B)) | ((k4_xboole_0 @ sk_B @ sk_C) = (sk_B)))),
% 0.37/0.55      inference('demod', [status(thm)], ['61', '62'])).
% 0.37/0.55  thf('64', plain, (((sk_B) != (sk_C))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('65', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 0.37/0.55  thf('66', plain,
% 0.37/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['33', '34'])).
% 0.37/0.55  thf('67', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['35', '36'])).
% 0.37/0.55  thf('68', plain, (((sk_C) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['52', '65', '66', '67'])).
% 0.37/0.55  thf('69', plain, (((sk_C) != (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('70', plain, ($false),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
