%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AfaDMSFuvO

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:22 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 154 expanded)
%              Number of leaves         :   31 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  606 (1501 expanded)
%              Number of equality atoms :   64 ( 109 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t59_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ( r1_tarski @ B @ C )
             => ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t59_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( ( B != k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = ( k6_setfam_1 @ A @ B ) ) )
        & ( ( B = k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = A ) ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X20 @ X19 )
        = ( k6_setfam_1 @ X20 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('3',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k6_setfam_1 @ sk_A @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k6_setfam_1 @ X24 @ X23 )
        = ( k1_setfam_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('6',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k1_setfam_1 @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X20 @ X19 )
        = ( k6_setfam_1 @ X20 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('10',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k6_setfam_1 @ X24 @ X23 )
        = ( k1_setfam_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('13',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B )
    = ( k1_setfam_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( r1_tarski @ X31 @ X32 )
      | ( r1_tarski @ ( k1_setfam_1 @ X32 ) @ ( k1_setfam_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('20',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['17','20'])).

thf('23',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('33',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('36',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_B )
    = sk_C ),
    inference('sup-',[status(thm)],['31','40'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('47',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B = sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45','48'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','49'])).

thf('51',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X20 @ X19 )
        = X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('53',plain,(
    ! [X20: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) )
      | ( ( k8_setfam_1 @ X20 @ k1_xboole_0 )
        = X20 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('54',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('55',plain,(
    ! [X20: $i] :
      ( ( k8_setfam_1 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('57',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('58',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('59',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('60',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51','55','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AfaDMSFuvO
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.76  % Solved by: fo/fo7.sh
% 0.54/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.76  % done 654 iterations in 0.306s
% 0.54/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.76  % SZS output start Refutation
% 0.54/0.76  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.54/0.76  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.54/0.76  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.54/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.76  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.54/0.76  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.54/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.76  thf(t59_setfam_1, conjecture,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.54/0.76       ( ![C:$i]:
% 0.54/0.76         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.54/0.76           ( ( r1_tarski @ B @ C ) =>
% 0.54/0.76             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.54/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.76    (~( ![A:$i,B:$i]:
% 0.54/0.76        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.54/0.76          ( ![C:$i]:
% 0.54/0.76            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.54/0.76              ( ( r1_tarski @ B @ C ) =>
% 0.54/0.76                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.54/0.76    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.54/0.76  thf('0', plain,
% 0.54/0.76      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('1', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(d10_setfam_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.54/0.76       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.54/0.76           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.54/0.76         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.54/0.76  thf('2', plain,
% 0.54/0.76      (![X19 : $i, X20 : $i]:
% 0.54/0.76         (((X19) = (k1_xboole_0))
% 0.54/0.76          | ((k8_setfam_1 @ X20 @ X19) = (k6_setfam_1 @ X20 @ X19))
% 0.54/0.76          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.54/0.76      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.54/0.76  thf('3', plain,
% 0.54/0.76      ((((k8_setfam_1 @ sk_A @ sk_C) = (k6_setfam_1 @ sk_A @ sk_C))
% 0.54/0.76        | ((sk_C) = (k1_xboole_0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.76  thf('4', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(redefinition_k6_setfam_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.54/0.76       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.54/0.76  thf('5', plain,
% 0.54/0.76      (![X23 : $i, X24 : $i]:
% 0.54/0.76         (((k6_setfam_1 @ X24 @ X23) = (k1_setfam_1 @ X23))
% 0.54/0.76          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24))))),
% 0.54/0.76      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.54/0.76  thf('6', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.54/0.76      inference('sup-', [status(thm)], ['4', '5'])).
% 0.54/0.76  thf('7', plain,
% 0.54/0.76      ((((k8_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))
% 0.54/0.76        | ((sk_C) = (k1_xboole_0)))),
% 0.54/0.76      inference('demod', [status(thm)], ['3', '6'])).
% 0.54/0.76  thf('8', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('9', plain,
% 0.54/0.76      (![X19 : $i, X20 : $i]:
% 0.54/0.76         (((X19) = (k1_xboole_0))
% 0.54/0.76          | ((k8_setfam_1 @ X20 @ X19) = (k6_setfam_1 @ X20 @ X19))
% 0.54/0.76          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.54/0.76      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.54/0.76  thf('10', plain,
% 0.54/0.76      ((((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))
% 0.54/0.76        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['8', '9'])).
% 0.54/0.76  thf('11', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('12', plain,
% 0.54/0.76      (![X23 : $i, X24 : $i]:
% 0.54/0.76         (((k6_setfam_1 @ X24 @ X23) = (k1_setfam_1 @ X23))
% 0.54/0.76          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24))))),
% 0.54/0.76      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.54/0.76  thf('13', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.54/0.76      inference('sup-', [status(thm)], ['11', '12'])).
% 0.54/0.76  thf('14', plain,
% 0.54/0.76      ((((k8_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))
% 0.54/0.76        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.76      inference('demod', [status(thm)], ['10', '13'])).
% 0.54/0.76  thf('15', plain,
% 0.54/0.76      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k8_setfam_1 @ sk_A @ sk_B))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('16', plain,
% 0.54/0.76      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.54/0.76        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.76  thf('17', plain,
% 0.54/0.76      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.54/0.76        | ((sk_C) = (k1_xboole_0))
% 0.54/0.76        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['7', '16'])).
% 0.54/0.76  thf('18', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(t7_setfam_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( r1_tarski @ A @ B ) =>
% 0.54/0.76       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.54/0.76         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.54/0.76  thf('19', plain,
% 0.54/0.76      (![X31 : $i, X32 : $i]:
% 0.54/0.76         (((X31) = (k1_xboole_0))
% 0.54/0.76          | ~ (r1_tarski @ X31 @ X32)
% 0.54/0.76          | (r1_tarski @ (k1_setfam_1 @ X32) @ (k1_setfam_1 @ X31)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.54/0.76  thf('20', plain,
% 0.54/0.76      (((r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B))
% 0.54/0.76        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['18', '19'])).
% 0.54/0.76  thf('21', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.54/0.76      inference('clc', [status(thm)], ['17', '20'])).
% 0.54/0.76  thf('22', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.54/0.76      inference('clc', [status(thm)], ['17', '20'])).
% 0.54/0.76  thf('23', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(t36_xboole_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.54/0.76  thf('24', plain,
% 0.54/0.76      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.54/0.76      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.54/0.76  thf(t1_xboole_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.54/0.76       ( r1_tarski @ A @ C ) ))).
% 0.54/0.76  thf('25', plain,
% 0.54/0.76      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.54/0.76         (~ (r1_tarski @ X6 @ X7)
% 0.54/0.76          | ~ (r1_tarski @ X7 @ X8)
% 0.54/0.76          | (r1_tarski @ X6 @ X8))),
% 0.54/0.76      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.54/0.76  thf('26', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.76         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.54/0.76      inference('sup-', [status(thm)], ['24', '25'])).
% 0.54/0.76  thf('27', plain,
% 0.54/0.76      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_C)),
% 0.54/0.76      inference('sup-', [status(thm)], ['23', '26'])).
% 0.54/0.76  thf(t79_xboole_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.54/0.76  thf('28', plain,
% 0.54/0.76      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 0.54/0.76      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.54/0.76  thf(t69_xboole_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.54/0.76       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.54/0.76  thf('29', plain,
% 0.54/0.76      (![X12 : $i, X13 : $i]:
% 0.54/0.76         (~ (r1_xboole_0 @ X12 @ X13)
% 0.54/0.76          | ~ (r1_tarski @ X12 @ X13)
% 0.54/0.76          | (v1_xboole_0 @ X12))),
% 0.54/0.76      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.54/0.76  thf('30', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 0.54/0.76          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['28', '29'])).
% 0.54/0.76  thf('31', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.54/0.76      inference('sup-', [status(thm)], ['27', '30'])).
% 0.54/0.76  thf(l13_xboole_0, axiom,
% 0.54/0.76    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.54/0.76  thf('32', plain,
% 0.54/0.76      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.54/0.76      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.54/0.76  thf(t4_boole, axiom,
% 0.54/0.76    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.54/0.76  thf('33', plain,
% 0.54/0.76      (![X11 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.54/0.76      inference('cnf', [status(esa)], [t4_boole])).
% 0.54/0.76  thf(t98_xboole_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.54/0.76  thf('34', plain,
% 0.54/0.76      (![X16 : $i, X17 : $i]:
% 0.54/0.76         ((k2_xboole_0 @ X16 @ X17)
% 0.54/0.76           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.54/0.76  thf('35', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.76      inference('sup+', [status(thm)], ['33', '34'])).
% 0.54/0.76  thf(t1_boole, axiom,
% 0.54/0.76    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.54/0.76  thf('36', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.54/0.76      inference('cnf', [status(esa)], [t1_boole])).
% 0.54/0.76  thf('37', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.54/0.76      inference('sup+', [status(thm)], ['35', '36'])).
% 0.54/0.76  thf('38', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         (((k5_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.76      inference('sup+', [status(thm)], ['32', '37'])).
% 0.54/0.76  thf('39', plain,
% 0.54/0.76      (![X16 : $i, X17 : $i]:
% 0.54/0.76         ((k2_xboole_0 @ X16 @ X17)
% 0.54/0.76           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.54/0.76  thf('40', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         (((k2_xboole_0 @ X0 @ X1) = (X0))
% 0.54/0.76          | ~ (v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.76      inference('sup+', [status(thm)], ['38', '39'])).
% 0.54/0.76  thf('41', plain, (((k2_xboole_0 @ sk_C @ sk_B) = (sk_C))),
% 0.54/0.76      inference('sup-', [status(thm)], ['31', '40'])).
% 0.54/0.76  thf(commutativity_k2_xboole_0, axiom,
% 0.54/0.76    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.54/0.76  thf('42', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.54/0.76      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.54/0.76  thf('43', plain, (((k2_xboole_0 @ sk_B @ sk_C) = (sk_C))),
% 0.54/0.76      inference('demod', [status(thm)], ['41', '42'])).
% 0.54/0.76  thf('44', plain,
% 0.54/0.76      ((((k2_xboole_0 @ sk_B @ k1_xboole_0) = (sk_C))
% 0.54/0.76        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.76      inference('sup+', [status(thm)], ['22', '43'])).
% 0.54/0.76  thf('45', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.54/0.76      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.54/0.76  thf('46', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.54/0.76      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.54/0.76  thf('47', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.54/0.76      inference('cnf', [status(esa)], [t1_boole])).
% 0.54/0.76  thf('48', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.76      inference('sup+', [status(thm)], ['46', '47'])).
% 0.54/0.76  thf('49', plain, ((((sk_B) = (sk_C)) | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.76      inference('demod', [status(thm)], ['44', '45', '48'])).
% 0.54/0.76  thf('50', plain,
% 0.54/0.76      ((((sk_B) = (k1_xboole_0))
% 0.54/0.76        | ((sk_B) = (k1_xboole_0))
% 0.54/0.76        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.76      inference('sup+', [status(thm)], ['21', '49'])).
% 0.54/0.76  thf('51', plain, (((sk_B) = (k1_xboole_0))),
% 0.54/0.76      inference('simplify', [status(thm)], ['50'])).
% 0.54/0.76  thf('52', plain,
% 0.54/0.76      (![X19 : $i, X20 : $i]:
% 0.54/0.76         (((X19) != (k1_xboole_0))
% 0.54/0.76          | ((k8_setfam_1 @ X20 @ X19) = (X20))
% 0.54/0.76          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.54/0.76      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.54/0.76  thf('53', plain,
% 0.54/0.76      (![X20 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20)))
% 0.54/0.76          | ((k8_setfam_1 @ X20 @ k1_xboole_0) = (X20)))),
% 0.54/0.76      inference('simplify', [status(thm)], ['52'])).
% 0.54/0.76  thf(t4_subset_1, axiom,
% 0.54/0.76    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.54/0.76  thf('54', plain,
% 0.54/0.76      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.54/0.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.54/0.76  thf('55', plain, (![X20 : $i]: ((k8_setfam_1 @ X20 @ k1_xboole_0) = (X20))),
% 0.54/0.76      inference('demod', [status(thm)], ['53', '54'])).
% 0.54/0.76  thf('56', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(dt_k8_setfam_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.54/0.76       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.54/0.76  thf('57', plain,
% 0.54/0.76      (![X21 : $i, X22 : $i]:
% 0.54/0.76         ((m1_subset_1 @ (k8_setfam_1 @ X21 @ X22) @ (k1_zfmisc_1 @ X21))
% 0.54/0.76          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 0.54/0.76      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.54/0.76  thf('58', plain,
% 0.54/0.76      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['56', '57'])).
% 0.54/0.76  thf(t3_subset, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.76  thf('59', plain,
% 0.54/0.76      (![X25 : $i, X26 : $i]:
% 0.54/0.76         ((r1_tarski @ X25 @ X26) | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.76  thf('60', plain, ((r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.54/0.76      inference('sup-', [status(thm)], ['58', '59'])).
% 0.54/0.76  thf('61', plain, ($false),
% 0.54/0.76      inference('demod', [status(thm)], ['0', '51', '55', '60'])).
% 0.54/0.76  
% 0.54/0.76  % SZS output end Refutation
% 0.54/0.76  
% 0.62/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
