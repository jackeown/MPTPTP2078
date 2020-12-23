%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KB0Jyx7xhi

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:33 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :  165 (2662 expanded)
%              Number of leaves         :   26 ( 811 expanded)
%              Depth                    :   38
%              Number of atoms          : 1258 (27023 expanded)
%              Number of equality atoms :  182 (3685 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t134_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ C @ D ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( ( A = C )
            & ( B = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t134_zfmisc_1])).

thf('0',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X48 @ X47 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('2',plain,
    ( ( ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('14',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X53 @ X55 ) @ X54 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X53 @ X54 ) @ ( k2_zfmisc_1 @ X55 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) )
      = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('18',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X57 @ X59 ) @ ( k3_xboole_0 @ X58 @ X60 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X57 @ X58 ) @ ( k2_zfmisc_1 @ X59 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
      = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['12','19'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('21',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ( r1_tarski @ X51 @ X52 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X50 @ X51 ) @ ( k2_zfmisc_1 @ X50 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
      | ( sk_C_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_D_1 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','22'])).

thf('24',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('25',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['12','19'])).

thf('26',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ( r1_tarski @ X51 @ X52 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X50 @ X51 ) @ ( k2_zfmisc_1 @ X50 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) )
      | ( r1_tarski @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) @ X0 )
      | ( sk_C_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_D_1 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    | ( sk_D_1
      = ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,
    ( ( sk_D_1
      = ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ sk_D_1 @ sk_B_1 )
      = ( k5_xboole_0 @ sk_D_1 @ sk_D_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X16: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X18 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('38',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('39',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ sk_D_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ( ( k4_xboole_0 @ X16 @ X17 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_D_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_tarski @ sk_D_1 @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('46',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_xboole_0 @ X22 @ X21 )
        = X21 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('47',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k2_xboole_0 @ sk_D_1 @ sk_B_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X53: $i,X55: $i,X56: $i] :
      ( ( k2_zfmisc_1 @ X56 @ ( k2_xboole_0 @ X53 @ X55 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X56 @ X53 ) @ ( k2_zfmisc_1 @ X56 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('49',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
      | ( sk_C_1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ( r1_tarski @ X51 @ X52 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X51 @ X50 ) @ ( k2_zfmisc_1 @ X52 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_xboole_0 @ X22 @ X21 )
        = X21 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('59',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k2_xboole_0 @ sk_A @ sk_C_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('61',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('63',plain,(
    ! [X53: $i,X55: $i,X56: $i] :
      ( ( k2_zfmisc_1 @ X56 @ ( k2_xboole_0 @ X53 @ X55 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X56 @ X53 ) @ ( k2_zfmisc_1 @ X56 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('64',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ ( k2_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('66',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ ( k2_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ( r1_tarski @ X51 @ X52 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X51 @ X50 ) @ ( k2_zfmisc_1 @ X52 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_A )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ ( k2_xboole_0 @ sk_D_1 @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('74',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('75',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('76',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('77',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_D_1
      = ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('79',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('80',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_xboole_0 @ X22 @ X21 )
        = X21 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
      = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('83',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ sk_D_1 )
      = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','83'])).

thf('85',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_D_1 )
      = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','84'])).

thf('86',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_D_1 )
      = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ( r1_tarski @ X51 @ X52 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X50 @ X51 ) @ ( k2_zfmisc_1 @ X50 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('94',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( r1_tarski @ sk_D_1 @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('96',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('97',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_B_1 @ sk_D_1 )
    | ( sk_B_1 = sk_D_1 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = sk_D_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,
    ( ( sk_B_1 = sk_D_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('101',plain,(
    ! [X25: $i] :
      ( ( k3_xboole_0 @ X25 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_C_1 @ X0 )
        = k1_xboole_0 )
      | ( sk_B_1 = sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
      = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('105',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
      = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_B_1 = sk_D_1 ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k2_zfmisc_1 @ X48 @ X49 )
        = k1_xboole_0 )
      | ( X48 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('107',plain,(
    ! [X49: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X49 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_B_1 = sk_D_1 ) ),
    inference(demod,[status(thm)],['105','107'])).

thf('109',plain,(
    ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3','4'])).

thf('110',plain,(
    sk_B_1 = sk_D_1 ),
    inference('simplify_reflect-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('112',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('113',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['72','110','111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('115',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['113','118'])).

thf('120',plain,
    ( ( sk_C_1 = sk_A )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','119'])).

thf('121',plain,
    ( ( sk_A != sk_C_1 )
    | ( sk_B_1 != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['121'])).

thf('123',plain,(
    sk_B_1 = sk_D_1 ),
    inference('simplify_reflect-',[status(thm)],['108','109'])).

thf('124',plain,
    ( ( sk_B_1 != sk_D_1 )
   <= ( sk_B_1 != sk_D_1 ) ),
    inference(split,[status(esa)],['121'])).

thf('125',plain,
    ( ( sk_D_1 != sk_D_1 )
   <= ( sk_B_1 != sk_D_1 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    sk_B_1 = sk_D_1 ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( sk_A != sk_C_1 )
    | ( sk_B_1 != sk_D_1 ) ),
    inference(split,[status(esa)],['121'])).

thf('128',plain,(
    sk_A != sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['126','127'])).

thf('129',plain,(
    sk_A != sk_C_1 ),
    inference(simpl_trail,[status(thm)],['122','128'])).

thf('130',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['120','129'])).

thf('131',plain,(
    ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 )
 != sk_C_1 ),
    inference(demod,[status(thm)],['5','130'])).

thf('132',plain,(
    ! [X49: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X49 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('133',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['120','129'])).

thf('134',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['120','129'])).

thf('135',plain,(
    ! [X49: $i] :
      ( ( k2_zfmisc_1 @ sk_C_1 @ X49 )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,(
    sk_C_1 != sk_C_1 ),
    inference(demod,[status(thm)],['131','135'])).

thf('137',plain,(
    $false ),
    inference(simplify,[status(thm)],['136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KB0Jyx7xhi
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:24:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.80/1.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.80/1.02  % Solved by: fo/fo7.sh
% 0.80/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/1.02  % done 1832 iterations in 0.575s
% 0.80/1.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.80/1.02  % SZS output start Refutation
% 0.80/1.02  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.80/1.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.80/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.80/1.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.80/1.02  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.80/1.02  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.80/1.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.80/1.02  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.80/1.02  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.80/1.02  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.80/1.02  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.80/1.02  thf(t134_zfmisc_1, conjecture,
% 0.80/1.02    (![A:$i,B:$i,C:$i,D:$i]:
% 0.80/1.02     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.80/1.02       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.80/1.02         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 0.80/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.02    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.80/1.02        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.80/1.02          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.80/1.02            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 0.80/1.02    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 0.80/1.02  thf('0', plain,
% 0.80/1.02      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf(t113_zfmisc_1, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.80/1.02       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.80/1.02  thf('1', plain,
% 0.80/1.02      (![X47 : $i, X48 : $i]:
% 0.80/1.02         (((X47) = (k1_xboole_0))
% 0.80/1.02          | ((X48) = (k1_xboole_0))
% 0.80/1.02          | ((k2_zfmisc_1 @ X48 @ X47) != (k1_xboole_0)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.80/1.02  thf('2', plain,
% 0.80/1.02      ((((k2_zfmisc_1 @ sk_C_1 @ sk_D_1) != (k1_xboole_0))
% 0.80/1.02        | ((sk_A) = (k1_xboole_0))
% 0.80/1.02        | ((sk_B_1) = (k1_xboole_0)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['0', '1'])).
% 0.80/1.02  thf('3', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('4', plain, (((sk_A) != (k1_xboole_0))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('5', plain, (((k2_zfmisc_1 @ sk_C_1 @ sk_D_1) != (k1_xboole_0))),
% 0.80/1.02      inference('simplify_reflect-', [status(thm)], ['2', '3', '4'])).
% 0.80/1.02  thf(d10_xboole_0, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.80/1.02  thf('6', plain,
% 0.80/1.02      (![X13 : $i, X14 : $i]: ((r1_tarski @ X13 @ X14) | ((X13) != (X14)))),
% 0.80/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.80/1.02  thf('7', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.80/1.02      inference('simplify', [status(thm)], ['6'])).
% 0.80/1.02  thf(commutativity_k2_xboole_0, axiom,
% 0.80/1.02    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.80/1.02  thf('8', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.80/1.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.80/1.02  thf(t7_xboole_1, axiom,
% 0.80/1.02    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.80/1.02  thf('9', plain,
% 0.80/1.02      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 0.80/1.02      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.80/1.02  thf(t28_xboole_1, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.80/1.02  thf('10', plain,
% 0.80/1.02      (![X23 : $i, X24 : $i]:
% 0.80/1.02         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.80/1.02      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.80/1.02  thf('11', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.80/1.02      inference('sup-', [status(thm)], ['9', '10'])).
% 0.80/1.02  thf('12', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.80/1.02      inference('sup+', [status(thm)], ['8', '11'])).
% 0.80/1.02  thf('13', plain,
% 0.80/1.02      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf(t120_zfmisc_1, axiom,
% 0.80/1.02    (![A:$i,B:$i,C:$i]:
% 0.80/1.02     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.80/1.02         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.80/1.02       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.80/1.02         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.80/1.02  thf('14', plain,
% 0.80/1.02      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.80/1.02         ((k2_zfmisc_1 @ (k2_xboole_0 @ X53 @ X55) @ X54)
% 0.80/1.02           = (k2_xboole_0 @ (k2_zfmisc_1 @ X53 @ X54) @ 
% 0.80/1.02              (k2_zfmisc_1 @ X55 @ X54)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.80/1.02  thf('15', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         ((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 0.80/1.02           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 0.80/1.02              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['13', '14'])).
% 0.80/1.02  thf('16', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.80/1.02      inference('sup-', [status(thm)], ['9', '10'])).
% 0.80/1.02  thf('17', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 0.80/1.02           (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B_1))
% 0.80/1.02           = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 0.80/1.02      inference('sup+', [status(thm)], ['15', '16'])).
% 0.80/1.02  thf(t123_zfmisc_1, axiom,
% 0.80/1.02    (![A:$i,B:$i,C:$i,D:$i]:
% 0.80/1.02     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.80/1.02       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.80/1.02  thf('18', plain,
% 0.80/1.02      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 0.80/1.02         ((k2_zfmisc_1 @ (k3_xboole_0 @ X57 @ X59) @ (k3_xboole_0 @ X58 @ X60))
% 0.80/1.02           = (k3_xboole_0 @ (k2_zfmisc_1 @ X57 @ X58) @ 
% 0.80/1.02              (k2_zfmisc_1 @ X59 @ X60)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.80/1.02  thf('19', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ X0)) @ 
% 0.80/1.02           (k3_xboole_0 @ sk_D_1 @ sk_B_1)) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 0.80/1.02      inference('demod', [status(thm)], ['17', '18'])).
% 0.80/1.02  thf('20', plain,
% 0.80/1.02      (((k2_zfmisc_1 @ sk_C_1 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 0.80/1.02         = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 0.80/1.02      inference('sup+', [status(thm)], ['12', '19'])).
% 0.80/1.02  thf(t117_zfmisc_1, axiom,
% 0.80/1.02    (![A:$i,B:$i,C:$i]:
% 0.80/1.02     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.80/1.02          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.80/1.02            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.80/1.02          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 0.80/1.02  thf('21', plain,
% 0.80/1.02      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.80/1.02         (((X50) = (k1_xboole_0))
% 0.80/1.02          | (r1_tarski @ X51 @ X52)
% 0.80/1.02          | ~ (r1_tarski @ (k2_zfmisc_1 @ X50 @ X51) @ 
% 0.80/1.02               (k2_zfmisc_1 @ X50 @ X52)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.80/1.02  thf('22', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ X0) @ 
% 0.80/1.02             (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 0.80/1.02          | (r1_tarski @ X0 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 0.80/1.02          | ((sk_C_1) = (k1_xboole_0)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['20', '21'])).
% 0.80/1.02  thf('23', plain,
% 0.80/1.02      ((((sk_C_1) = (k1_xboole_0))
% 0.80/1.02        | (r1_tarski @ sk_D_1 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['7', '22'])).
% 0.80/1.02  thf('24', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.80/1.02      inference('simplify', [status(thm)], ['6'])).
% 0.80/1.02  thf('25', plain,
% 0.80/1.02      (((k2_zfmisc_1 @ sk_C_1 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 0.80/1.02         = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 0.80/1.02      inference('sup+', [status(thm)], ['12', '19'])).
% 0.80/1.02  thf('26', plain,
% 0.80/1.02      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.80/1.02         (((X50) = (k1_xboole_0))
% 0.80/1.02          | (r1_tarski @ X51 @ X52)
% 0.80/1.02          | ~ (r1_tarski @ (k2_zfmisc_1 @ X50 @ X51) @ 
% 0.80/1.02               (k2_zfmisc_1 @ X50 @ X52)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.80/1.02  thf('27', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 0.80/1.02             (k2_zfmisc_1 @ sk_C_1 @ X0))
% 0.80/1.02          | (r1_tarski @ (k3_xboole_0 @ sk_D_1 @ sk_B_1) @ X0)
% 0.80/1.02          | ((sk_C_1) = (k1_xboole_0)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['25', '26'])).
% 0.80/1.02  thf('28', plain,
% 0.80/1.02      ((((sk_C_1) = (k1_xboole_0))
% 0.80/1.02        | (r1_tarski @ (k3_xboole_0 @ sk_D_1 @ sk_B_1) @ sk_D_1))),
% 0.80/1.02      inference('sup-', [status(thm)], ['24', '27'])).
% 0.80/1.02  thf('29', plain,
% 0.80/1.02      (![X13 : $i, X15 : $i]:
% 0.80/1.02         (((X13) = (X15))
% 0.80/1.02          | ~ (r1_tarski @ X15 @ X13)
% 0.80/1.02          | ~ (r1_tarski @ X13 @ X15))),
% 0.80/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.80/1.02  thf('30', plain,
% 0.80/1.02      ((((sk_C_1) = (k1_xboole_0))
% 0.80/1.02        | ~ (r1_tarski @ sk_D_1 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 0.80/1.02        | ((sk_D_1) = (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['28', '29'])).
% 0.80/1.02  thf('31', plain,
% 0.80/1.02      ((((sk_C_1) = (k1_xboole_0))
% 0.80/1.02        | ((sk_D_1) = (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 0.80/1.02        | ((sk_C_1) = (k1_xboole_0)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['23', '30'])).
% 0.80/1.02  thf('32', plain,
% 0.80/1.02      ((((sk_D_1) = (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 0.80/1.02        | ((sk_C_1) = (k1_xboole_0)))),
% 0.80/1.02      inference('simplify', [status(thm)], ['31'])).
% 0.80/1.02  thf(t100_xboole_1, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.80/1.02  thf('33', plain,
% 0.80/1.02      (![X19 : $i, X20 : $i]:
% 0.80/1.02         ((k4_xboole_0 @ X19 @ X20)
% 0.80/1.02           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.80/1.02  thf('34', plain,
% 0.80/1.02      ((((k4_xboole_0 @ sk_D_1 @ sk_B_1) = (k5_xboole_0 @ sk_D_1 @ sk_D_1))
% 0.80/1.02        | ((sk_C_1) = (k1_xboole_0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['32', '33'])).
% 0.80/1.02  thf('35', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.80/1.02      inference('simplify', [status(thm)], ['6'])).
% 0.80/1.02  thf(l32_xboole_1, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.80/1.02  thf('36', plain,
% 0.80/1.02      (![X16 : $i, X18 : $i]:
% 0.80/1.02         (((k4_xboole_0 @ X16 @ X18) = (k1_xboole_0))
% 0.80/1.02          | ~ (r1_tarski @ X16 @ X18))),
% 0.80/1.02      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.80/1.02  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.80/1.02      inference('sup-', [status(thm)], ['35', '36'])).
% 0.80/1.02  thf(idempotence_k3_xboole_0, axiom,
% 0.80/1.02    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.80/1.02  thf('38', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.80/1.02      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.80/1.02  thf('39', plain,
% 0.80/1.02      (![X19 : $i, X20 : $i]:
% 0.80/1.02         ((k4_xboole_0 @ X19 @ X20)
% 0.80/1.02           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.80/1.02  thf('40', plain,
% 0.80/1.02      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.80/1.02      inference('sup+', [status(thm)], ['38', '39'])).
% 0.80/1.02  thf('41', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.80/1.02      inference('demod', [status(thm)], ['37', '40'])).
% 0.80/1.02  thf('42', plain,
% 0.80/1.02      ((((k4_xboole_0 @ sk_D_1 @ sk_B_1) = (k1_xboole_0))
% 0.80/1.02        | ((sk_C_1) = (k1_xboole_0)))),
% 0.80/1.02      inference('demod', [status(thm)], ['34', '41'])).
% 0.80/1.02  thf('43', plain,
% 0.80/1.02      (![X16 : $i, X17 : $i]:
% 0.80/1.02         ((r1_tarski @ X16 @ X17)
% 0.80/1.02          | ((k4_xboole_0 @ X16 @ X17) != (k1_xboole_0)))),
% 0.80/1.02      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.80/1.02  thf('44', plain,
% 0.80/1.02      ((((k1_xboole_0) != (k1_xboole_0))
% 0.80/1.02        | ((sk_C_1) = (k1_xboole_0))
% 0.80/1.02        | (r1_tarski @ sk_D_1 @ sk_B_1))),
% 0.80/1.02      inference('sup-', [status(thm)], ['42', '43'])).
% 0.80/1.02  thf('45', plain,
% 0.80/1.02      (((r1_tarski @ sk_D_1 @ sk_B_1) | ((sk_C_1) = (k1_xboole_0)))),
% 0.80/1.02      inference('simplify', [status(thm)], ['44'])).
% 0.80/1.02  thf(t12_xboole_1, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.80/1.02  thf('46', plain,
% 0.80/1.02      (![X21 : $i, X22 : $i]:
% 0.80/1.02         (((k2_xboole_0 @ X22 @ X21) = (X21)) | ~ (r1_tarski @ X22 @ X21))),
% 0.80/1.02      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.80/1.02  thf('47', plain,
% 0.80/1.02      ((((sk_C_1) = (k1_xboole_0))
% 0.80/1.02        | ((k2_xboole_0 @ sk_D_1 @ sk_B_1) = (sk_B_1)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['45', '46'])).
% 0.80/1.02  thf('48', plain,
% 0.80/1.02      (![X53 : $i, X55 : $i, X56 : $i]:
% 0.80/1.02         ((k2_zfmisc_1 @ X56 @ (k2_xboole_0 @ X53 @ X55))
% 0.80/1.02           = (k2_xboole_0 @ (k2_zfmisc_1 @ X56 @ X53) @ 
% 0.80/1.02              (k2_zfmisc_1 @ X56 @ X55)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.80/1.02  thf('49', plain,
% 0.80/1.02      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 0.80/1.02      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.80/1.02  thf('50', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.02         (r1_tarski @ (k2_zfmisc_1 @ X2 @ X1) @ 
% 0.80/1.02          (k2_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['48', '49'])).
% 0.80/1.02  thf('51', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         ((r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_D_1) @ 
% 0.80/1.02           (k2_zfmisc_1 @ X0 @ sk_B_1))
% 0.80/1.02          | ((sk_C_1) = (k1_xboole_0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['47', '50'])).
% 0.80/1.02  thf('52', plain,
% 0.80/1.02      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('53', plain,
% 0.80/1.02      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.80/1.02         (((X50) = (k1_xboole_0))
% 0.80/1.02          | (r1_tarski @ X51 @ X52)
% 0.80/1.02          | ~ (r1_tarski @ (k2_zfmisc_1 @ X51 @ X50) @ 
% 0.80/1.02               (k2_zfmisc_1 @ X52 @ X50)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.80/1.02  thf('54', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 0.80/1.02             (k2_zfmisc_1 @ X0 @ sk_B_1))
% 0.80/1.02          | (r1_tarski @ sk_A @ X0)
% 0.80/1.02          | ((sk_B_1) = (k1_xboole_0)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['52', '53'])).
% 0.80/1.02  thf('55', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('56', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 0.80/1.02             (k2_zfmisc_1 @ X0 @ sk_B_1))
% 0.80/1.02          | (r1_tarski @ sk_A @ X0))),
% 0.80/1.02      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.80/1.02  thf('57', plain,
% 0.80/1.02      ((((sk_C_1) = (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_C_1))),
% 0.80/1.02      inference('sup-', [status(thm)], ['51', '56'])).
% 0.80/1.02  thf('58', plain,
% 0.80/1.02      (![X21 : $i, X22 : $i]:
% 0.80/1.02         (((k2_xboole_0 @ X22 @ X21) = (X21)) | ~ (r1_tarski @ X22 @ X21))),
% 0.80/1.02      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.80/1.02  thf('59', plain,
% 0.80/1.02      ((((sk_C_1) = (k1_xboole_0)) | ((k2_xboole_0 @ sk_A @ sk_C_1) = (sk_C_1)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['57', '58'])).
% 0.80/1.02  thf('60', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.80/1.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.80/1.02  thf('61', plain,
% 0.80/1.02      ((((sk_C_1) = (k1_xboole_0)) | ((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1)))),
% 0.80/1.02      inference('demod', [status(thm)], ['59', '60'])).
% 0.80/1.02  thf('62', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         ((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 0.80/1.02           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 0.80/1.02              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['13', '14'])).
% 0.80/1.02  thf('63', plain,
% 0.80/1.02      (![X53 : $i, X55 : $i, X56 : $i]:
% 0.80/1.02         ((k2_zfmisc_1 @ X56 @ (k2_xboole_0 @ X53 @ X55))
% 0.80/1.02           = (k2_xboole_0 @ (k2_zfmisc_1 @ X56 @ X53) @ 
% 0.80/1.02              (k2_zfmisc_1 @ X56 @ X55)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.80/1.02  thf('64', plain,
% 0.80/1.02      (((k2_zfmisc_1 @ sk_C_1 @ (k2_xboole_0 @ sk_D_1 @ sk_B_1))
% 0.80/1.02         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B_1))),
% 0.80/1.02      inference('sup+', [status(thm)], ['62', '63'])).
% 0.80/1.02  thf('65', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.80/1.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.80/1.02  thf('66', plain,
% 0.80/1.02      (((k2_zfmisc_1 @ sk_C_1 @ (k2_xboole_0 @ sk_D_1 @ sk_B_1))
% 0.80/1.02         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B_1))),
% 0.80/1.02      inference('demod', [status(thm)], ['64', '65'])).
% 0.80/1.02  thf('67', plain,
% 0.80/1.02      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('68', plain,
% 0.80/1.02      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.80/1.02         (((X50) = (k1_xboole_0))
% 0.80/1.02          | (r1_tarski @ X51 @ X52)
% 0.80/1.02          | ~ (r1_tarski @ (k2_zfmisc_1 @ X51 @ X50) @ 
% 0.80/1.02               (k2_zfmisc_1 @ X52 @ X50)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.80/1.02  thf('69', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B_1) @ 
% 0.80/1.02             (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 0.80/1.02          | (r1_tarski @ X0 @ sk_A)
% 0.80/1.02          | ((sk_B_1) = (k1_xboole_0)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['67', '68'])).
% 0.80/1.02  thf('70', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('71', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B_1) @ 
% 0.80/1.02             (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 0.80/1.02          | (r1_tarski @ X0 @ sk_A))),
% 0.80/1.02      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 0.80/1.02  thf('72', plain,
% 0.80/1.02      ((~ (r1_tarski @ 
% 0.80/1.02           (k2_zfmisc_1 @ sk_C_1 @ (k2_xboole_0 @ sk_D_1 @ sk_B_1)) @ 
% 0.80/1.02           (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 0.80/1.02        | (r1_tarski @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_A))),
% 0.80/1.02      inference('sup-', [status(thm)], ['66', '71'])).
% 0.80/1.02  thf('73', plain,
% 0.80/1.02      ((((sk_C_1) = (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_C_1))),
% 0.80/1.02      inference('sup-', [status(thm)], ['51', '56'])).
% 0.80/1.02  thf('74', plain,
% 0.80/1.02      (![X23 : $i, X24 : $i]:
% 0.80/1.02         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.80/1.02      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.80/1.02  thf('75', plain,
% 0.80/1.02      ((((sk_C_1) = (k1_xboole_0)) | ((k3_xboole_0 @ sk_A @ sk_C_1) = (sk_A)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['73', '74'])).
% 0.80/1.02  thf(commutativity_k3_xboole_0, axiom,
% 0.80/1.02    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.80/1.02  thf('76', plain,
% 0.80/1.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.80/1.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/1.02  thf('77', plain,
% 0.80/1.02      ((((sk_C_1) = (k1_xboole_0)) | ((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_A)))),
% 0.80/1.02      inference('demod', [status(thm)], ['75', '76'])).
% 0.80/1.02  thf('78', plain,
% 0.80/1.02      ((((sk_D_1) = (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 0.80/1.02        | ((sk_C_1) = (k1_xboole_0)))),
% 0.80/1.02      inference('simplify', [status(thm)], ['31'])).
% 0.80/1.02  thf('79', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.80/1.02      inference('simplify', [status(thm)], ['6'])).
% 0.80/1.02  thf('80', plain,
% 0.80/1.02      (![X21 : $i, X22 : $i]:
% 0.80/1.02         (((k2_xboole_0 @ X22 @ X21) = (X21)) | ~ (r1_tarski @ X22 @ X21))),
% 0.80/1.02      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.80/1.02  thf('81', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.80/1.02      inference('sup-', [status(thm)], ['79', '80'])).
% 0.80/1.02  thf('82', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ X0)) @ 
% 0.80/1.02           (k3_xboole_0 @ sk_D_1 @ sk_B_1)) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 0.80/1.02      inference('demod', [status(thm)], ['17', '18'])).
% 0.80/1.02  thf('83', plain,
% 0.80/1.02      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 0.80/1.02         (k3_xboole_0 @ sk_D_1 @ sk_B_1)) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 0.80/1.02      inference('sup+', [status(thm)], ['81', '82'])).
% 0.80/1.02  thf('84', plain,
% 0.80/1.02      ((((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ sk_D_1)
% 0.80/1.02          = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 0.80/1.02        | ((sk_C_1) = (k1_xboole_0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['78', '83'])).
% 0.80/1.02  thf('85', plain,
% 0.80/1.02      ((((k2_zfmisc_1 @ sk_A @ sk_D_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 0.80/1.02        | ((sk_C_1) = (k1_xboole_0))
% 0.80/1.02        | ((sk_C_1) = (k1_xboole_0)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['77', '84'])).
% 0.80/1.02  thf('86', plain,
% 0.80/1.02      ((((sk_C_1) = (k1_xboole_0))
% 0.80/1.02        | ((k2_zfmisc_1 @ sk_A @ sk_D_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1)))),
% 0.80/1.02      inference('simplify', [status(thm)], ['85'])).
% 0.80/1.02  thf('87', plain,
% 0.80/1.02      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('88', plain,
% 0.80/1.02      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.80/1.02         (((X50) = (k1_xboole_0))
% 0.80/1.02          | (r1_tarski @ X51 @ X52)
% 0.80/1.02          | ~ (r1_tarski @ (k2_zfmisc_1 @ X50 @ X51) @ 
% 0.80/1.02               (k2_zfmisc_1 @ X50 @ X52)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.80/1.02  thf('89', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 0.80/1.02             (k2_zfmisc_1 @ sk_A @ X0))
% 0.80/1.02          | (r1_tarski @ sk_B_1 @ X0)
% 0.80/1.02          | ((sk_A) = (k1_xboole_0)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['87', '88'])).
% 0.80/1.02  thf('90', plain, (((sk_A) != (k1_xboole_0))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('91', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 0.80/1.02             (k2_zfmisc_1 @ sk_A @ X0))
% 0.80/1.02          | (r1_tarski @ sk_B_1 @ X0))),
% 0.80/1.02      inference('simplify_reflect-', [status(thm)], ['89', '90'])).
% 0.80/1.02  thf('92', plain,
% 0.80/1.02      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 0.80/1.02           (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 0.80/1.02        | ((sk_C_1) = (k1_xboole_0))
% 0.80/1.02        | (r1_tarski @ sk_B_1 @ sk_D_1))),
% 0.80/1.02      inference('sup-', [status(thm)], ['86', '91'])).
% 0.80/1.02  thf('93', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.80/1.02      inference('simplify', [status(thm)], ['6'])).
% 0.80/1.02  thf('94', plain,
% 0.80/1.02      ((((sk_C_1) = (k1_xboole_0)) | (r1_tarski @ sk_B_1 @ sk_D_1))),
% 0.80/1.02      inference('demod', [status(thm)], ['92', '93'])).
% 0.80/1.02  thf('95', plain,
% 0.80/1.02      (((r1_tarski @ sk_D_1 @ sk_B_1) | ((sk_C_1) = (k1_xboole_0)))),
% 0.80/1.02      inference('simplify', [status(thm)], ['44'])).
% 0.80/1.02  thf('96', plain,
% 0.80/1.02      (![X13 : $i, X15 : $i]:
% 0.80/1.02         (((X13) = (X15))
% 0.80/1.02          | ~ (r1_tarski @ X15 @ X13)
% 0.80/1.02          | ~ (r1_tarski @ X13 @ X15))),
% 0.80/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.80/1.02  thf('97', plain,
% 0.80/1.02      ((((sk_C_1) = (k1_xboole_0))
% 0.80/1.02        | ~ (r1_tarski @ sk_B_1 @ sk_D_1)
% 0.80/1.02        | ((sk_B_1) = (sk_D_1)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['95', '96'])).
% 0.80/1.02  thf('98', plain,
% 0.80/1.02      ((((sk_C_1) = (k1_xboole_0))
% 0.80/1.02        | ((sk_B_1) = (sk_D_1))
% 0.80/1.02        | ((sk_C_1) = (k1_xboole_0)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['94', '97'])).
% 0.80/1.02  thf('99', plain, ((((sk_B_1) = (sk_D_1)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.80/1.02      inference('simplify', [status(thm)], ['98'])).
% 0.80/1.02  thf('100', plain,
% 0.80/1.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.80/1.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/1.02  thf(t2_boole, axiom,
% 0.80/1.02    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.80/1.02  thf('101', plain,
% 0.80/1.02      (![X25 : $i]: ((k3_xboole_0 @ X25 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/1.02      inference('cnf', [status(esa)], [t2_boole])).
% 0.80/1.02  thf('102', plain,
% 0.80/1.02      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.80/1.02      inference('sup+', [status(thm)], ['100', '101'])).
% 0.80/1.02  thf('103', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (((k3_xboole_0 @ sk_C_1 @ X0) = (k1_xboole_0)) | ((sk_B_1) = (sk_D_1)))),
% 0.80/1.02      inference('sup+', [status(thm)], ['99', '102'])).
% 0.80/1.02  thf('104', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ X0)) @ 
% 0.80/1.02           (k3_xboole_0 @ sk_D_1 @ sk_B_1)) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 0.80/1.03      inference('demod', [status(thm)], ['17', '18'])).
% 0.80/1.03  thf('105', plain,
% 0.80/1.03      ((((k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 0.80/1.03          = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 0.80/1.03        | ((sk_B_1) = (sk_D_1)))),
% 0.80/1.03      inference('sup+', [status(thm)], ['103', '104'])).
% 0.80/1.03  thf('106', plain,
% 0.80/1.03      (![X48 : $i, X49 : $i]:
% 0.80/1.03         (((k2_zfmisc_1 @ X48 @ X49) = (k1_xboole_0))
% 0.80/1.03          | ((X48) != (k1_xboole_0)))),
% 0.80/1.03      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.80/1.03  thf('107', plain,
% 0.80/1.03      (![X49 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X49) = (k1_xboole_0))),
% 0.80/1.03      inference('simplify', [status(thm)], ['106'])).
% 0.80/1.03  thf('108', plain,
% 0.80/1.03      ((((k1_xboole_0) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 0.80/1.03        | ((sk_B_1) = (sk_D_1)))),
% 0.80/1.03      inference('demod', [status(thm)], ['105', '107'])).
% 0.80/1.03  thf('109', plain, (((k2_zfmisc_1 @ sk_C_1 @ sk_D_1) != (k1_xboole_0))),
% 0.80/1.03      inference('simplify_reflect-', [status(thm)], ['2', '3', '4'])).
% 0.80/1.03  thf('110', plain, (((sk_B_1) = (sk_D_1))),
% 0.80/1.03      inference('simplify_reflect-', [status(thm)], ['108', '109'])).
% 0.80/1.03  thf('111', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['79', '80'])).
% 0.80/1.03  thf('112', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.80/1.03      inference('simplify', [status(thm)], ['6'])).
% 0.80/1.03  thf('113', plain, ((r1_tarski @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_A)),
% 0.80/1.03      inference('demod', [status(thm)], ['72', '110', '111', '112'])).
% 0.80/1.03  thf('114', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.80/1.03      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.80/1.03  thf('115', plain,
% 0.80/1.03      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 0.80/1.03      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.80/1.03  thf('116', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.80/1.03      inference('sup+', [status(thm)], ['114', '115'])).
% 0.80/1.03  thf('117', plain,
% 0.80/1.03      (![X13 : $i, X15 : $i]:
% 0.80/1.03         (((X13) = (X15))
% 0.80/1.03          | ~ (r1_tarski @ X15 @ X13)
% 0.80/1.03          | ~ (r1_tarski @ X13 @ X15))),
% 0.80/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.80/1.03  thf('118', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.80/1.03          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['116', '117'])).
% 0.80/1.03  thf('119', plain, (((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 0.80/1.03      inference('sup-', [status(thm)], ['113', '118'])).
% 0.80/1.03  thf('120', plain, ((((sk_C_1) = (sk_A)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.80/1.03      inference('sup+', [status(thm)], ['61', '119'])).
% 0.80/1.03  thf('121', plain, ((((sk_A) != (sk_C_1)) | ((sk_B_1) != (sk_D_1)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('122', plain, ((((sk_A) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 0.80/1.03      inference('split', [status(esa)], ['121'])).
% 0.80/1.03  thf('123', plain, (((sk_B_1) = (sk_D_1))),
% 0.80/1.03      inference('simplify_reflect-', [status(thm)], ['108', '109'])).
% 0.80/1.03  thf('124', plain, ((((sk_B_1) != (sk_D_1))) <= (~ (((sk_B_1) = (sk_D_1))))),
% 0.80/1.03      inference('split', [status(esa)], ['121'])).
% 0.80/1.03  thf('125', plain, ((((sk_D_1) != (sk_D_1))) <= (~ (((sk_B_1) = (sk_D_1))))),
% 0.80/1.03      inference('sup-', [status(thm)], ['123', '124'])).
% 0.80/1.03  thf('126', plain, ((((sk_B_1) = (sk_D_1)))),
% 0.80/1.03      inference('simplify', [status(thm)], ['125'])).
% 0.80/1.03  thf('127', plain, (~ (((sk_A) = (sk_C_1))) | ~ (((sk_B_1) = (sk_D_1)))),
% 0.80/1.03      inference('split', [status(esa)], ['121'])).
% 0.80/1.03  thf('128', plain, (~ (((sk_A) = (sk_C_1)))),
% 0.80/1.03      inference('sat_resolution*', [status(thm)], ['126', '127'])).
% 0.80/1.03  thf('129', plain, (((sk_A) != (sk_C_1))),
% 0.80/1.03      inference('simpl_trail', [status(thm)], ['122', '128'])).
% 0.80/1.03  thf('130', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.80/1.03      inference('simplify_reflect-', [status(thm)], ['120', '129'])).
% 0.80/1.03  thf('131', plain, (((k2_zfmisc_1 @ sk_C_1 @ sk_D_1) != (sk_C_1))),
% 0.80/1.03      inference('demod', [status(thm)], ['5', '130'])).
% 0.80/1.03  thf('132', plain,
% 0.80/1.03      (![X49 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X49) = (k1_xboole_0))),
% 0.80/1.03      inference('simplify', [status(thm)], ['106'])).
% 0.80/1.03  thf('133', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.80/1.03      inference('simplify_reflect-', [status(thm)], ['120', '129'])).
% 0.80/1.03  thf('134', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.80/1.03      inference('simplify_reflect-', [status(thm)], ['120', '129'])).
% 0.80/1.03  thf('135', plain, (![X49 : $i]: ((k2_zfmisc_1 @ sk_C_1 @ X49) = (sk_C_1))),
% 0.80/1.03      inference('demod', [status(thm)], ['132', '133', '134'])).
% 0.80/1.03  thf('136', plain, (((sk_C_1) != (sk_C_1))),
% 0.80/1.03      inference('demod', [status(thm)], ['131', '135'])).
% 0.80/1.03  thf('137', plain, ($false), inference('simplify', [status(thm)], ['136'])).
% 0.80/1.03  
% 0.80/1.03  % SZS output end Refutation
% 0.80/1.03  
% 0.80/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
