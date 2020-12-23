%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3czDOSuOkg

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:20 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 759 expanded)
%              Number of leaves         :   28 ( 233 expanded)
%              Depth                    :   16
%              Number of atoms          :  693 (7836 expanded)
%              Number of equality atoms :   68 ( 524 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X16 @ X15 )
        = ( k6_setfam_1 @ X16 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( ( k6_setfam_1 @ X20 @ X19 )
        = ( k1_setfam_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
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
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X16 @ X15 )
        = ( k6_setfam_1 @ X16 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('10',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B_1 )
      = ( k6_setfam_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k6_setfam_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k6_setfam_1 @ X20 @ X19 )
        = ( k1_setfam_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('15',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B_1 )
    = ( k1_setfam_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( r1_tarski @ X28 @ X29 )
      | ( r1_tarski @ ( k1_setfam_1 @ X29 ) @ ( k1_setfam_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('20',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ ( k1_setfam_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['17','20'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('24',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( sk_B @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_B @ ( k1_zfmisc_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( sk_B @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','32'])).

thf('34',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B_1 )
    | ( sk_C = sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( sk_C = sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('42',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_C = sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['37','42'])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','43'])).

thf('45',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( sk_B @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ X8 )
        = X8 )
      | ~ ( r2_hidden @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('50',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ X11 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = sk_B_1 ) ),
    inference(demod,[status(thm)],['44','52'])).

thf('54',plain,
    ( ( k1_xboole_0 = sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','53'])).

thf('55',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X16 @ X15 )
        = X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('60',plain,(
    ! [X16: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) )
      | ( ( k8_setfam_1 @ X16 @ k1_xboole_0 )
        = X16 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k8_setfam_1 @ X1 @ k1_xboole_0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,
    ( ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
      = sk_A )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(simplify,[status(thm)],['54'])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['51'])).

thf('65',plain,
    ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_A ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['56','65'])).

thf('67',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k1_setfam_1 @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('68',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['56','65'])).

thf('69',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k6_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('71',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k6_setfam_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_setfam_1])).

thf('72',plain,(
    m1_subset_1 @ ( k6_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('74',plain,(
    r1_tarski @ ( k6_setfam_1 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('76',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','76'])).

thf('78',plain,
    ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_A ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('79',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('80',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['66','77','78','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3czDOSuOkg
% 0.17/0.37  % Computer   : n001.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 11:41:15 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.37  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 211 iterations in 0.142s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.62  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.41/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.62  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.41/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.62  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.41/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.62  thf(t59_setfam_1, conjecture,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62       ( ![C:$i]:
% 0.41/0.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62           ( ( r1_tarski @ B @ C ) =>
% 0.41/0.62             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i,B:$i]:
% 0.41/0.62        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62          ( ![C:$i]:
% 0.41/0.62            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62              ( ( r1_tarski @ B @ C ) =>
% 0.41/0.62                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.41/0.62  thf('0', plain,
% 0.41/0.62      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.41/0.62          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('1', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(d10_setfam_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.41/0.62           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.41/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      (![X15 : $i, X16 : $i]:
% 0.41/0.62         (((X15) = (k1_xboole_0))
% 0.41/0.62          | ((k8_setfam_1 @ X16 @ X15) = (k6_setfam_1 @ X16 @ X15))
% 0.41/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.41/0.62      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      ((((k8_setfam_1 @ sk_A @ sk_C) = (k6_setfam_1 @ sk_A @ sk_C))
% 0.41/0.62        | ((sk_C) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.62  thf('4', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(redefinition_k6_setfam_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      (![X19 : $i, X20 : $i]:
% 0.41/0.62         (((k6_setfam_1 @ X20 @ X19) = (k1_setfam_1 @ X19))
% 0.41/0.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.41/0.62  thf('6', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.41/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      ((((k8_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))
% 0.41/0.62        | ((sk_C) = (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['3', '6'])).
% 0.41/0.62  thf('8', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      (![X15 : $i, X16 : $i]:
% 0.41/0.62         (((X15) = (k1_xboole_0))
% 0.41/0.62          | ((k8_setfam_1 @ X16 @ X15) = (k6_setfam_1 @ X16 @ X15))
% 0.41/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.41/0.62      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | ((sk_B_1) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.41/0.62  thf('11', plain,
% 0.41/0.62      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.41/0.62          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.41/0.62           (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.41/0.62        | ((sk_B_1) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('14', plain,
% 0.41/0.62      (![X19 : $i, X20 : $i]:
% 0.41/0.62         (((k6_setfam_1 @ X20 @ X19) = (k1_setfam_1 @ X19))
% 0.41/0.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.41/0.62  thf('15', plain, (((k6_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.41/0.62  thf('16', plain,
% 0.41/0.62      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_setfam_1 @ sk_B_1))
% 0.41/0.62        | ((sk_B_1) = (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['12', '15'])).
% 0.41/0.62  thf('17', plain,
% 0.41/0.62      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B_1))
% 0.41/0.62        | ((sk_C) = (k1_xboole_0))
% 0.41/0.62        | ((sk_B_1) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['7', '16'])).
% 0.41/0.62  thf('18', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(t7_setfam_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( r1_tarski @ A @ B ) =>
% 0.41/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.41/0.62         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.41/0.62  thf('19', plain,
% 0.41/0.62      (![X28 : $i, X29 : $i]:
% 0.41/0.62         (((X28) = (k1_xboole_0))
% 0.41/0.62          | ~ (r1_tarski @ X28 @ X29)
% 0.41/0.62          | (r1_tarski @ (k1_setfam_1 @ X29) @ (k1_setfam_1 @ X28)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.41/0.62  thf('20', plain,
% 0.41/0.62      (((r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B_1))
% 0.41/0.62        | ((sk_B_1) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.62  thf('21', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.41/0.62      inference('clc', [status(thm)], ['17', '20'])).
% 0.41/0.62  thf('22', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.41/0.62      inference('clc', [status(thm)], ['17', '20'])).
% 0.41/0.62  thf(l13_xboole_0, axiom,
% 0.41/0.62    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.62  thf('23', plain,
% 0.41/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.41/0.62  thf(existence_m1_subset_1, axiom,
% 0.41/0.62    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.41/0.62  thf('24', plain, (![X12 : $i]: (m1_subset_1 @ (sk_B @ X12) @ X12)),
% 0.41/0.62      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.41/0.62  thf(cc1_subset_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( v1_xboole_0 @ A ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.41/0.62  thf('25', plain,
% 0.41/0.62      (![X13 : $i, X14 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.41/0.62          | (v1_xboole_0 @ X13)
% 0.41/0.62          | ~ (v1_xboole_0 @ X14))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.41/0.62  thf('26', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (sk_B @ (k1_zfmisc_1 @ X0))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.41/0.62  thf('27', plain,
% 0.41/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.41/0.62  thf('28', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (v1_xboole_0 @ X0) | ((sk_B @ (k1_zfmisc_1 @ X0)) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.41/0.62  thf('29', plain, (![X12 : $i]: (m1_subset_1 @ (sk_B @ X12) @ X12)),
% 0.41/0.62      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.41/0.62  thf(t3_subset, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.62  thf('30', plain,
% 0.41/0.62      (![X25 : $i, X26 : $i]:
% 0.41/0.62         ((r1_tarski @ X25 @ X26) | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.62  thf('31', plain,
% 0.41/0.62      (![X0 : $i]: (r1_tarski @ (sk_B @ (k1_zfmisc_1 @ X0)) @ X0)),
% 0.41/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.41/0.62  thf('32', plain,
% 0.41/0.62      (![X0 : $i]: ((r1_tarski @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['28', '31'])).
% 0.41/0.62  thf('33', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.62      inference('sup+', [status(thm)], ['23', '32'])).
% 0.41/0.62  thf('34', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(d10_xboole_0, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.62  thf('35', plain,
% 0.41/0.62      (![X1 : $i, X3 : $i]:
% 0.41/0.62         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.41/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.62  thf('36', plain, ((~ (r1_tarski @ sk_C @ sk_B_1) | ((sk_C) = (sk_B_1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.41/0.62  thf('37', plain,
% 0.41/0.62      ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_C) | ((sk_C) = (sk_B_1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['33', '36'])).
% 0.41/0.62  thf('38', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('39', plain,
% 0.41/0.62      (![X25 : $i, X27 : $i]:
% 0.41/0.62         ((m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X27)) | ~ (r1_tarski @ X25 @ X27))),
% 0.41/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.62  thf('40', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_C))),
% 0.41/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.41/0.62  thf('41', plain,
% 0.41/0.62      (![X13 : $i, X14 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.41/0.62          | (v1_xboole_0 @ X13)
% 0.41/0.62          | ~ (v1_xboole_0 @ X14))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.41/0.62  thf('42', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['40', '41'])).
% 0.41/0.62  thf('43', plain, ((((sk_C) = (sk_B_1)) | ~ (v1_xboole_0 @ sk_C))),
% 0.41/0.62      inference('clc', [status(thm)], ['37', '42'])).
% 0.41/0.62  thf('44', plain,
% 0.41/0.62      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.41/0.62        | ((sk_B_1) = (k1_xboole_0))
% 0.41/0.62        | ((sk_C) = (sk_B_1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['22', '43'])).
% 0.41/0.62  thf('45', plain, (![X12 : $i]: (m1_subset_1 @ (sk_B @ X12) @ X12)),
% 0.41/0.62      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.41/0.62  thf(t2_subset, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ A @ B ) =>
% 0.41/0.62       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.41/0.62  thf('46', plain,
% 0.41/0.62      (![X23 : $i, X24 : $i]:
% 0.41/0.62         ((r2_hidden @ X23 @ X24)
% 0.41/0.62          | (v1_xboole_0 @ X24)
% 0.41/0.62          | ~ (m1_subset_1 @ X23 @ X24))),
% 0.41/0.62      inference('cnf', [status(esa)], [t2_subset])).
% 0.41/0.62  thf('47', plain,
% 0.41/0.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.41/0.62  thf(l22_zfmisc_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( r2_hidden @ A @ B ) =>
% 0.41/0.62       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.41/0.62  thf('48', plain,
% 0.41/0.62      (![X8 : $i, X9 : $i]:
% 0.41/0.62         (((k2_xboole_0 @ (k1_tarski @ X9) @ X8) = (X8))
% 0.41/0.62          | ~ (r2_hidden @ X9 @ X8))),
% 0.41/0.62      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.41/0.62  thf('49', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((v1_xboole_0 @ X0)
% 0.41/0.62          | ((k2_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0) = (X0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['47', '48'])).
% 0.41/0.62  thf(t49_zfmisc_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.41/0.62  thf('50', plain,
% 0.41/0.62      (![X10 : $i, X11 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k1_tarski @ X10) @ X11) != (k1_xboole_0))),
% 0.41/0.62      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.41/0.62  thf('51', plain,
% 0.41/0.62      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (v1_xboole_0 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.41/0.62  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.62      inference('simplify', [status(thm)], ['51'])).
% 0.41/0.62  thf('53', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_C) = (sk_B_1)))),
% 0.41/0.62      inference('demod', [status(thm)], ['44', '52'])).
% 0.41/0.62  thf('54', plain,
% 0.41/0.62      ((((k1_xboole_0) = (sk_B_1))
% 0.41/0.62        | ((sk_B_1) = (k1_xboole_0))
% 0.41/0.62        | ((sk_B_1) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['21', '53'])).
% 0.41/0.62  thf('55', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.41/0.62      inference('simplify', [status(thm)], ['54'])).
% 0.41/0.62  thf('56', plain,
% 0.41/0.62      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.41/0.62          (k8_setfam_1 @ sk_A @ k1_xboole_0))),
% 0.41/0.62      inference('demod', [status(thm)], ['0', '55'])).
% 0.41/0.62  thf('57', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('58', plain,
% 0.41/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.41/0.62  thf('59', plain,
% 0.41/0.62      (![X15 : $i, X16 : $i]:
% 0.41/0.62         (((X15) != (k1_xboole_0))
% 0.41/0.62          | ((k8_setfam_1 @ X16 @ X15) = (X16))
% 0.41/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.41/0.62      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.41/0.62  thf('60', plain,
% 0.41/0.62      (![X16 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16)))
% 0.41/0.62          | ((k8_setfam_1 @ X16 @ k1_xboole_0) = (X16)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['59'])).
% 0.41/0.62  thf('61', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1)))
% 0.41/0.62          | ~ (v1_xboole_0 @ X0)
% 0.41/0.62          | ((k8_setfam_1 @ X1 @ k1_xboole_0) = (X1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['58', '60'])).
% 0.41/0.62  thf('62', plain,
% 0.41/0.62      ((((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A))
% 0.41/0.62        | ~ (v1_xboole_0 @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['57', '61'])).
% 0.41/0.62  thf('63', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.41/0.62      inference('simplify', [status(thm)], ['54'])).
% 0.41/0.62  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.62      inference('simplify', [status(thm)], ['51'])).
% 0.41/0.62  thf('65', plain, (((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.41/0.62  thf('66', plain, (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.41/0.62      inference('demod', [status(thm)], ['56', '65'])).
% 0.41/0.62  thf('67', plain,
% 0.41/0.62      ((((k8_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))
% 0.41/0.62        | ((sk_C) = (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['3', '6'])).
% 0.41/0.62  thf('68', plain, (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.41/0.62      inference('demod', [status(thm)], ['56', '65'])).
% 0.41/0.62  thf('69', plain,
% 0.41/0.62      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ sk_A) | ((sk_C) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['67', '68'])).
% 0.41/0.62  thf('70', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(dt_k6_setfam_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62       ( m1_subset_1 @ ( k6_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.41/0.62  thf('71', plain,
% 0.41/0.62      (![X17 : $i, X18 : $i]:
% 0.41/0.62         ((m1_subset_1 @ (k6_setfam_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 0.41/0.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k6_setfam_1])).
% 0.41/0.62  thf('72', plain,
% 0.41/0.62      ((m1_subset_1 @ (k6_setfam_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['70', '71'])).
% 0.41/0.62  thf('73', plain,
% 0.41/0.62      (![X25 : $i, X26 : $i]:
% 0.41/0.62         ((r1_tarski @ X25 @ X26) | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.62  thf('74', plain, ((r1_tarski @ (k6_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.41/0.62      inference('sup-', [status(thm)], ['72', '73'])).
% 0.41/0.62  thf('75', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.41/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.62  thf('76', plain, ((r1_tarski @ (k1_setfam_1 @ sk_C) @ sk_A)),
% 0.41/0.62      inference('demod', [status(thm)], ['74', '75'])).
% 0.41/0.62  thf('77', plain, (((sk_C) = (k1_xboole_0))),
% 0.41/0.62      inference('demod', [status(thm)], ['69', '76'])).
% 0.41/0.62  thf('78', plain, (((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.41/0.62  thf('79', plain,
% 0.41/0.62      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.41/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.62  thf('80', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.41/0.62      inference('simplify', [status(thm)], ['79'])).
% 0.41/0.62  thf('81', plain, ($false),
% 0.41/0.62      inference('demod', [status(thm)], ['66', '77', '78', '80'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
