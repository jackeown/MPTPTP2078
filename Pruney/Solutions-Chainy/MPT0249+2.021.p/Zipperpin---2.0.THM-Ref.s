%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NIe90M0Kcf

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 282 expanded)
%              Number of leaves         :   30 (  98 expanded)
%              Depth                    :   20
%              Number of atoms          :  620 (2147 expanded)
%              Number of equality atoms :   82 ( 374 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
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
    ! [X49: $i,X50: $i] :
      ( ( X50
        = ( k1_tarski @ X49 ) )
      | ( X50 = k1_xboole_0 )
      | ~ ( r1_tarski @ X50 @ ( k1_tarski @ X49 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('25',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('30',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','31'])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['14','32'])).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('37',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('38',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('39',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k3_tarski @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,
    ( sk_B
    = ( k1_tarski @ ( k3_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','44'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('46',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X47 ) @ X48 )
      | ( r2_hidden @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r2_hidden @ ( k3_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r2_hidden @ ( k3_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('49',plain,(
    ! [X54: $i,X56: $i,X57: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X54 @ X56 ) @ X57 )
      | ~ ( r2_hidden @ X56 @ X57 )
      | ~ ( r2_hidden @ X54 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_tarski @ ( k2_tarski @ X1 @ ( k3_tarski @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_tarski @ ( k2_tarski @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ sk_B ) ) @ X0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('53',plain,
    ( sk_B
    = ( k1_tarski @ ( k3_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','44'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('56',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_B = sk_C )
    | ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['36','57'])).

thf('59',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('61',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['35','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','31'])).

thf('65',plain,
    ( sk_C
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('68',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NIe90M0Kcf
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:58:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 259 iterations in 0.085s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(t44_zfmisc_1, conjecture,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.22/0.54          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.54          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.54        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.22/0.54             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.54             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.22/0.54  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t7_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.22/0.54      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.54  thf('3', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.22/0.54      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf(l3_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.22/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      (![X49 : $i, X50 : $i]:
% 0.22/0.54         (((X50) = (k1_tarski @ X49))
% 0.22/0.54          | ((X50) = (k1_xboole_0))
% 0.22/0.54          | ~ (r1_tarski @ X50 @ (k1_tarski @ X49)))),
% 0.22/0.54      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.22/0.54  thf('5', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.54  thf('6', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('7', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.22/0.54  thf('8', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.54      inference('demod', [status(thm)], ['0', '7'])).
% 0.22/0.54  thf(t95_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k3_xboole_0 @ A @ B ) =
% 0.22/0.54       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      (![X17 : $i, X18 : $i]:
% 0.22/0.54         ((k3_xboole_0 @ X17 @ X18)
% 0.22/0.54           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 0.22/0.54              (k2_xboole_0 @ X17 @ X18)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.22/0.54  thf(t91_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.54       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.54         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.22/0.54           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X17 : $i, X18 : $i]:
% 0.22/0.54         ((k3_xboole_0 @ X17 @ X18)
% 0.22/0.54           = (k5_xboole_0 @ X17 @ 
% 0.22/0.54              (k5_xboole_0 @ X18 @ (k2_xboole_0 @ X17 @ X18))))),
% 0.22/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.22/0.54         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ sk_B)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['8', '11'])).
% 0.22/0.54  thf(commutativity_k5_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.22/0.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.22/0.54         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.22/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.54  thf(t92_xboole_1, axiom,
% 0.22/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.54  thf('15', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.54         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.22/0.54           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.22/0.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.54         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.22/0.54           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['16', '17'])).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 0.22/0.54           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['15', '18'])).
% 0.22/0.54  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.54  thf('20', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.22/0.54      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.54  thf(t100_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (![X4 : $i, X5 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ X4 @ X5)
% 0.22/0.54           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['20', '21'])).
% 0.22/0.54  thf('23', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.54  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.54  thf(idempotence_k2_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.54  thf('25', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.22/0.54      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      (![X17 : $i, X18 : $i]:
% 0.22/0.54         ((k3_xboole_0 @ X17 @ X18)
% 0.22/0.54           = (k5_xboole_0 @ X17 @ 
% 0.22/0.54              (k5_xboole_0 @ X18 @ (k2_xboole_0 @ X17 @ X18))))),
% 0.22/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.54  thf('27', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k3_xboole_0 @ X0 @ X0)
% 0.22/0.54           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['25', '26'])).
% 0.22/0.54  thf('28', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.22/0.54      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['20', '21'])).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.22/0.54  thf('31', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['24', '30'])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['19', '31'])).
% 0.22/0.54  thf('33', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (sk_C))),
% 0.22/0.54      inference('demod', [status(thm)], ['14', '32'])).
% 0.22/0.54  thf('34', plain,
% 0.22/0.54      (![X4 : $i, X5 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ X4 @ X5)
% 0.22/0.54           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      (((k4_xboole_0 @ sk_B @ sk_C) = (k5_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.54      inference('sup+', [status(thm)], ['33', '34'])).
% 0.22/0.54  thf('36', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.54      inference('demod', [status(thm)], ['0', '7'])).
% 0.22/0.54  thf('37', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.22/0.54  thf('38', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.22/0.54  thf(t69_enumset1, axiom,
% 0.22/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.54  thf('39', plain,
% 0.22/0.54      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.22/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.54  thf(l51_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.54  thf('40', plain,
% 0.22/0.54      (![X52 : $i, X53 : $i]:
% 0.22/0.54         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 0.22/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['39', '40'])).
% 0.22/0.54  thf('42', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.22/0.54      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.22/0.54  thf('43', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.54  thf('44', plain, (((k3_tarski @ sk_B) = (sk_A))),
% 0.22/0.54      inference('sup+', [status(thm)], ['38', '43'])).
% 0.22/0.54  thf('45', plain, (((sk_B) = (k1_tarski @ (k3_tarski @ sk_B)))),
% 0.22/0.54      inference('demod', [status(thm)], ['37', '44'])).
% 0.22/0.54  thf(l27_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.22/0.54  thf('46', plain,
% 0.22/0.54      (![X47 : $i, X48 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ (k1_tarski @ X47) @ X48) | (r2_hidden @ X47 @ X48))),
% 0.22/0.54      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.22/0.54  thf('47', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ sk_B @ X0) | (r2_hidden @ (k3_tarski @ sk_B) @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['45', '46'])).
% 0.22/0.54  thf('48', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ sk_B @ X0) | (r2_hidden @ (k3_tarski @ sk_B) @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['45', '46'])).
% 0.22/0.54  thf(t38_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.22/0.54       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.22/0.54  thf('49', plain,
% 0.22/0.54      (![X54 : $i, X56 : $i, X57 : $i]:
% 0.22/0.54         ((r1_tarski @ (k2_tarski @ X54 @ X56) @ X57)
% 0.22/0.54          | ~ (r2_hidden @ X56 @ X57)
% 0.22/0.54          | ~ (r2_hidden @ X54 @ X57))),
% 0.22/0.54      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.22/0.54  thf('50', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ sk_B @ X0)
% 0.22/0.54          | ~ (r2_hidden @ X1 @ X0)
% 0.22/0.54          | (r1_tarski @ (k2_tarski @ X1 @ (k3_tarski @ sk_B)) @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.54  thf('51', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ sk_B @ X0)
% 0.22/0.54          | (r1_tarski @ 
% 0.22/0.54             (k2_tarski @ (k3_tarski @ sk_B) @ (k3_tarski @ sk_B)) @ X0)
% 0.22/0.54          | (r1_xboole_0 @ sk_B @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['47', '50'])).
% 0.22/0.54  thf('52', plain,
% 0.22/0.54      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.22/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.54  thf('53', plain, (((sk_B) = (k1_tarski @ (k3_tarski @ sk_B)))),
% 0.22/0.54      inference('demod', [status(thm)], ['37', '44'])).
% 0.22/0.54  thf('54', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ sk_B @ X0)
% 0.22/0.54          | (r1_tarski @ sk_B @ X0)
% 0.22/0.54          | (r1_xboole_0 @ sk_B @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.22/0.54  thf('55', plain,
% 0.22/0.54      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | (r1_xboole_0 @ sk_B @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['54'])).
% 0.22/0.54  thf(t12_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.54  thf('56', plain,
% 0.22/0.54      (![X6 : $i, X7 : $i]:
% 0.22/0.54         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.54  thf('57', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ sk_B @ X0) | ((k2_xboole_0 @ sk_B @ X0) = (X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.54  thf('58', plain, ((((sk_B) = (sk_C)) | (r1_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.54      inference('sup+', [status(thm)], ['36', '57'])).
% 0.22/0.54  thf('59', plain, (((sk_B) != (sk_C))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('60', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 0.22/0.54  thf(t83_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.54  thf('61', plain,
% 0.22/0.54      (![X10 : $i, X11 : $i]:
% 0.22/0.54         (((k4_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.22/0.54      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.54  thf('62', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['60', '61'])).
% 0.22/0.54  thf('63', plain, (((sk_B) = (k5_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.54      inference('demod', [status(thm)], ['35', '62'])).
% 0.22/0.54  thf('64', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['19', '31'])).
% 0.22/0.54  thf('65', plain, (((sk_C) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.22/0.54      inference('sup+', [status(thm)], ['63', '64'])).
% 0.22/0.54  thf('66', plain,
% 0.22/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['20', '21'])).
% 0.22/0.54  thf('67', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.54  thf('68', plain, (((sk_C) = (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.22/0.54  thf('69', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('70', plain, ($false),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
