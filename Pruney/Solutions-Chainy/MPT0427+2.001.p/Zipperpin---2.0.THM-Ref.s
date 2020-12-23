%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RoLL7jBq2o

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:20 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 805 expanded)
%              Number of leaves         :   27 ( 245 expanded)
%              Depth                    :   19
%              Number of atoms          :  709 (8287 expanded)
%              Number of equality atoms :   68 ( 544 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X20 @ X19 )
        = ( k6_setfam_1 @ X20 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( ( k6_setfam_1 @ X24 @ X23 )
        = ( k1_setfam_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( r1_tarski @ X30 @ X31 )
      | ( r1_tarski @ ( k1_setfam_1 @ X31 ) @ ( k1_setfam_1 @ X30 ) ) ) ),
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
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X27: $i,X29: $i] :
      ( ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(dt_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k6_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k6_setfam_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_setfam_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_setfam_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_xboole_0 @ X17 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_setfam_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_setfam_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_setfam_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('35',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_setfam_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','37'])).

thf('39',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B_1 )
    | ( sk_C = sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( sk_C = sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X27: $i,X29: $i] :
      ( ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_xboole_0 @ X17 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('47',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_C = sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['42','47'])).

thf('49',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','48'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('50',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('51',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ X13 )
        = X13 )
      | ~ ( r2_hidden @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('53',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ X16 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = sk_B_1 ) ),
    inference(demod,[status(thm)],['49','55'])).

thf('57',plain,
    ( ( k1_xboole_0 = sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','56'])).

thf('58',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ ( k8_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('62',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 != k1_xboole_0 )
      | ( ( k8_setfam_1 @ X20 @ X19 )
        = X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('63',plain,(
    ! [X20: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) )
      | ( ( k8_setfam_1 @ X20 @ k1_xboole_0 )
        = X20 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k8_setfam_1 @ X1 @ k1_xboole_0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,
    ( ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
      = sk_A )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','64'])).

thf('66',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(simplify,[status(thm)],['57'])).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf('68',plain,
    ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_A ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['59','68'])).

thf('70',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_C )
      = ( k1_setfam_1 @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('71',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['59','68'])).

thf('72',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ sk_C ) @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k6_setfam_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_setfam_1])).

thf('75',plain,(
    m1_subset_1 @ ( k6_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('77',plain,(
    r1_tarski @ ( k6_setfam_1 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('79',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['72','79'])).

thf('81',plain,
    ( ( k8_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_A ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('82',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['69','80','81','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RoLL7jBq2o
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.60  % Solved by: fo/fo7.sh
% 0.39/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.60  % done 190 iterations in 0.144s
% 0.39/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.60  % SZS output start Refutation
% 0.39/0.60  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.39/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.60  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.39/0.60  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.39/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.60  thf(t59_setfam_1, conjecture,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.60       ( ![C:$i]:
% 0.39/0.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.60           ( ( r1_tarski @ B @ C ) =>
% 0.39/0.60             ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ))).
% 0.39/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.60    (~( ![A:$i,B:$i]:
% 0.39/0.60        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.60          ( ![C:$i]:
% 0.39/0.60            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.60              ( ( r1_tarski @ B @ C ) =>
% 0.39/0.60                ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ) )),
% 0.39/0.60    inference('cnf.neg', [status(esa)], [t59_setfam_1])).
% 0.39/0.60  thf('0', plain,
% 0.39/0.60      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.39/0.60          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('1', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(d10_setfam_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.60       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.39/0.60           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.39/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.39/0.60  thf('2', plain,
% 0.39/0.60      (![X19 : $i, X20 : $i]:
% 0.39/0.60         (((X19) = (k1_xboole_0))
% 0.39/0.60          | ((k8_setfam_1 @ X20 @ X19) = (k6_setfam_1 @ X20 @ X19))
% 0.39/0.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.39/0.60      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.39/0.60  thf('3', plain,
% 0.39/0.60      ((((k8_setfam_1 @ sk_A @ sk_C) = (k6_setfam_1 @ sk_A @ sk_C))
% 0.39/0.60        | ((sk_C) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.60  thf('4', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(redefinition_k6_setfam_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.60       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.39/0.60  thf('5', plain,
% 0.39/0.60      (![X23 : $i, X24 : $i]:
% 0.39/0.60         (((k6_setfam_1 @ X24 @ X23) = (k1_setfam_1 @ X23))
% 0.39/0.60          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24))))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.39/0.60  thf('6', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.39/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.60  thf('7', plain,
% 0.39/0.60      ((((k8_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))
% 0.39/0.60        | ((sk_C) = (k1_xboole_0)))),
% 0.39/0.60      inference('demod', [status(thm)], ['3', '6'])).
% 0.39/0.60  thf('8', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('9', plain,
% 0.39/0.60      (![X19 : $i, X20 : $i]:
% 0.39/0.60         (((X19) = (k1_xboole_0))
% 0.39/0.60          | ((k8_setfam_1 @ X20 @ X19) = (k6_setfam_1 @ X20 @ X19))
% 0.39/0.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.39/0.60      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.39/0.60  thf('10', plain,
% 0.39/0.60      ((((k8_setfam_1 @ sk_A @ sk_B_1) = (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.39/0.60        | ((sk_B_1) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.60  thf('11', plain,
% 0.39/0.60      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.39/0.60          (k8_setfam_1 @ sk_A @ sk_B_1))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('12', plain,
% 0.39/0.60      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.39/0.60           (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.39/0.60        | ((sk_B_1) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.60  thf('13', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('14', plain,
% 0.39/0.60      (![X23 : $i, X24 : $i]:
% 0.39/0.60         (((k6_setfam_1 @ X24 @ X23) = (k1_setfam_1 @ X23))
% 0.39/0.60          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24))))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.39/0.60  thf('15', plain, (((k6_setfam_1 @ sk_A @ sk_B_1) = (k1_setfam_1 @ sk_B_1))),
% 0.39/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.60  thf('16', plain,
% 0.39/0.60      ((~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ (k1_setfam_1 @ sk_B_1))
% 0.39/0.60        | ((sk_B_1) = (k1_xboole_0)))),
% 0.39/0.60      inference('demod', [status(thm)], ['12', '15'])).
% 0.39/0.60  thf('17', plain,
% 0.39/0.60      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B_1))
% 0.39/0.60        | ((sk_C) = (k1_xboole_0))
% 0.39/0.60        | ((sk_B_1) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['7', '16'])).
% 0.39/0.60  thf('18', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(t7_setfam_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( r1_tarski @ A @ B ) =>
% 0.39/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.60         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.39/0.60  thf('19', plain,
% 0.39/0.60      (![X30 : $i, X31 : $i]:
% 0.39/0.60         (((X30) = (k1_xboole_0))
% 0.39/0.60          | ~ (r1_tarski @ X30 @ X31)
% 0.39/0.60          | (r1_tarski @ (k1_setfam_1 @ X31) @ (k1_setfam_1 @ X30)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t7_setfam_1])).
% 0.39/0.60  thf('20', plain,
% 0.39/0.60      (((r1_tarski @ (k1_setfam_1 @ sk_C) @ (k1_setfam_1 @ sk_B_1))
% 0.39/0.60        | ((sk_B_1) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.60  thf('21', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.39/0.60      inference('clc', [status(thm)], ['17', '20'])).
% 0.39/0.60  thf('22', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.39/0.60      inference('clc', [status(thm)], ['17', '20'])).
% 0.39/0.60  thf(l13_xboole_0, axiom,
% 0.39/0.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.60  thf('23', plain,
% 0.39/0.60      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.39/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.60  thf(d10_xboole_0, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.60  thf('24', plain,
% 0.39/0.60      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.39/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.60  thf('25', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.39/0.60      inference('simplify', [status(thm)], ['24'])).
% 0.39/0.60  thf(t3_subset, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.60  thf('26', plain,
% 0.39/0.60      (![X27 : $i, X29 : $i]:
% 0.39/0.60         ((m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X29)) | ~ (r1_tarski @ X27 @ X29))),
% 0.39/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.60  thf('27', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.60  thf(dt_k6_setfam_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.60       ( m1_subset_1 @ ( k6_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.39/0.60  thf('28', plain,
% 0.39/0.60      (![X21 : $i, X22 : $i]:
% 0.39/0.60         ((m1_subset_1 @ (k6_setfam_1 @ X21 @ X22) @ (k1_zfmisc_1 @ X21))
% 0.39/0.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 0.39/0.60      inference('cnf', [status(esa)], [dt_k6_setfam_1])).
% 0.39/0.60  thf('29', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (m1_subset_1 @ (k6_setfam_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ 
% 0.39/0.60          (k1_zfmisc_1 @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.60  thf(cc1_subset_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( v1_xboole_0 @ A ) =>
% 0.39/0.60       ( ![B:$i]:
% 0.39/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.39/0.60  thf('30', plain,
% 0.39/0.60      (![X17 : $i, X18 : $i]:
% 0.39/0.60         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.39/0.60          | (v1_xboole_0 @ X17)
% 0.39/0.60          | ~ (v1_xboole_0 @ X18))),
% 0.39/0.60      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.39/0.60  thf('31', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (v1_xboole_0 @ X0)
% 0.39/0.60          | (v1_xboole_0 @ (k6_setfam_1 @ X0 @ (k1_zfmisc_1 @ X0))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.60  thf('32', plain,
% 0.39/0.60      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.39/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.60  thf('33', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (v1_xboole_0 @ X0)
% 0.39/0.60          | ((k6_setfam_1 @ X0 @ (k1_zfmisc_1 @ X0)) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.60  thf('34', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (m1_subset_1 @ (k6_setfam_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ 
% 0.39/0.60          (k1_zfmisc_1 @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.60  thf('35', plain,
% 0.39/0.60      (![X27 : $i, X28 : $i]:
% 0.39/0.60         ((r1_tarski @ X27 @ X28) | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.60  thf('36', plain,
% 0.39/0.60      (![X0 : $i]: (r1_tarski @ (k6_setfam_1 @ X0 @ (k1_zfmisc_1 @ X0)) @ X0)),
% 0.39/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.39/0.60  thf('37', plain,
% 0.39/0.60      (![X0 : $i]: ((r1_tarski @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['33', '36'])).
% 0.39/0.60  thf('38', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.60      inference('sup+', [status(thm)], ['23', '37'])).
% 0.39/0.60  thf('39', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('40', plain,
% 0.39/0.60      (![X4 : $i, X6 : $i]:
% 0.39/0.60         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.39/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.60  thf('41', plain, ((~ (r1_tarski @ sk_C @ sk_B_1) | ((sk_C) = (sk_B_1)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.60  thf('42', plain,
% 0.39/0.60      ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_C) | ((sk_C) = (sk_B_1)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['38', '41'])).
% 0.39/0.60  thf('43', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('44', plain,
% 0.39/0.60      (![X27 : $i, X29 : $i]:
% 0.39/0.60         ((m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X29)) | ~ (r1_tarski @ X27 @ X29))),
% 0.39/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.60  thf('45', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_C))),
% 0.39/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.60  thf('46', plain,
% 0.39/0.60      (![X17 : $i, X18 : $i]:
% 0.39/0.60         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.39/0.60          | (v1_xboole_0 @ X17)
% 0.39/0.60          | ~ (v1_xboole_0 @ X18))),
% 0.39/0.60      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.39/0.60  thf('47', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B_1))),
% 0.39/0.60      inference('sup-', [status(thm)], ['45', '46'])).
% 0.39/0.60  thf('48', plain, ((((sk_C) = (sk_B_1)) | ~ (v1_xboole_0 @ sk_C))),
% 0.39/0.60      inference('clc', [status(thm)], ['42', '47'])).
% 0.39/0.60  thf('49', plain,
% 0.39/0.60      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.60        | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.60        | ((sk_C) = (sk_B_1)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['22', '48'])).
% 0.39/0.60  thf(d1_xboole_0, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.60  thf('50', plain,
% 0.39/0.60      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.60  thf(l22_zfmisc_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( r2_hidden @ A @ B ) =>
% 0.39/0.60       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.39/0.60  thf('51', plain,
% 0.39/0.60      (![X13 : $i, X14 : $i]:
% 0.39/0.60         (((k2_xboole_0 @ (k1_tarski @ X14) @ X13) = (X13))
% 0.39/0.60          | ~ (r2_hidden @ X14 @ X13))),
% 0.39/0.60      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.39/0.60  thf('52', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((v1_xboole_0 @ X0)
% 0.39/0.60          | ((k2_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0) = (X0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['50', '51'])).
% 0.39/0.60  thf(t49_zfmisc_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.39/0.60  thf('53', plain,
% 0.39/0.60      (![X15 : $i, X16 : $i]:
% 0.39/0.60         ((k2_xboole_0 @ (k1_tarski @ X15) @ X16) != (k1_xboole_0))),
% 0.39/0.60      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.39/0.60  thf('54', plain,
% 0.39/0.60      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (v1_xboole_0 @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['52', '53'])).
% 0.39/0.60  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.60      inference('simplify', [status(thm)], ['54'])).
% 0.39/0.60  thf('56', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_C) = (sk_B_1)))),
% 0.39/0.60      inference('demod', [status(thm)], ['49', '55'])).
% 0.39/0.60  thf('57', plain,
% 0.39/0.60      ((((k1_xboole_0) = (sk_B_1))
% 0.39/0.60        | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.60        | ((sk_B_1) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['21', '56'])).
% 0.39/0.60  thf('58', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.39/0.60      inference('simplify', [status(thm)], ['57'])).
% 0.39/0.60  thf('59', plain,
% 0.39/0.60      (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ 
% 0.39/0.60          (k8_setfam_1 @ sk_A @ k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['0', '58'])).
% 0.39/0.60  thf('60', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('61', plain,
% 0.39/0.60      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.39/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.60  thf('62', plain,
% 0.39/0.60      (![X19 : $i, X20 : $i]:
% 0.39/0.60         (((X19) != (k1_xboole_0))
% 0.39/0.60          | ((k8_setfam_1 @ X20 @ X19) = (X20))
% 0.39/0.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.39/0.60      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.39/0.60  thf('63', plain,
% 0.39/0.60      (![X20 : $i]:
% 0.39/0.60         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20)))
% 0.39/0.60          | ((k8_setfam_1 @ X20 @ k1_xboole_0) = (X20)))),
% 0.39/0.60      inference('simplify', [status(thm)], ['62'])).
% 0.39/0.60  thf('64', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1)))
% 0.39/0.60          | ~ (v1_xboole_0 @ X0)
% 0.39/0.60          | ((k8_setfam_1 @ X1 @ k1_xboole_0) = (X1)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['61', '63'])).
% 0.39/0.60  thf('65', plain,
% 0.39/0.60      ((((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A))
% 0.39/0.60        | ~ (v1_xboole_0 @ sk_B_1))),
% 0.39/0.60      inference('sup-', [status(thm)], ['60', '64'])).
% 0.39/0.60  thf('66', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.39/0.60      inference('simplify', [status(thm)], ['57'])).
% 0.39/0.60  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.60      inference('simplify', [status(thm)], ['54'])).
% 0.39/0.60  thf('68', plain, (((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A))),
% 0.39/0.60      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.39/0.60  thf('69', plain, (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.39/0.60      inference('demod', [status(thm)], ['59', '68'])).
% 0.39/0.60  thf('70', plain,
% 0.39/0.60      ((((k8_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))
% 0.39/0.60        | ((sk_C) = (k1_xboole_0)))),
% 0.39/0.60      inference('demod', [status(thm)], ['3', '6'])).
% 0.39/0.60  thf('71', plain, (~ (r1_tarski @ (k8_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.39/0.60      inference('demod', [status(thm)], ['59', '68'])).
% 0.39/0.60  thf('72', plain,
% 0.39/0.60      ((~ (r1_tarski @ (k1_setfam_1 @ sk_C) @ sk_A) | ((sk_C) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['70', '71'])).
% 0.39/0.60  thf('73', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('74', plain,
% 0.39/0.60      (![X21 : $i, X22 : $i]:
% 0.39/0.60         ((m1_subset_1 @ (k6_setfam_1 @ X21 @ X22) @ (k1_zfmisc_1 @ X21))
% 0.39/0.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 0.39/0.60      inference('cnf', [status(esa)], [dt_k6_setfam_1])).
% 0.39/0.60  thf('75', plain,
% 0.39/0.60      ((m1_subset_1 @ (k6_setfam_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.60      inference('sup-', [status(thm)], ['73', '74'])).
% 0.39/0.60  thf('76', plain,
% 0.39/0.60      (![X27 : $i, X28 : $i]:
% 0.39/0.60         ((r1_tarski @ X27 @ X28) | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.60  thf('77', plain, ((r1_tarski @ (k6_setfam_1 @ sk_A @ sk_C) @ sk_A)),
% 0.39/0.60      inference('sup-', [status(thm)], ['75', '76'])).
% 0.39/0.60  thf('78', plain, (((k6_setfam_1 @ sk_A @ sk_C) = (k1_setfam_1 @ sk_C))),
% 0.39/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.60  thf('79', plain, ((r1_tarski @ (k1_setfam_1 @ sk_C) @ sk_A)),
% 0.39/0.60      inference('demod', [status(thm)], ['77', '78'])).
% 0.39/0.60  thf('80', plain, (((sk_C) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['72', '79'])).
% 0.39/0.60  thf('81', plain, (((k8_setfam_1 @ sk_A @ k1_xboole_0) = (sk_A))),
% 0.39/0.60      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.39/0.60  thf('82', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.39/0.60      inference('simplify', [status(thm)], ['24'])).
% 0.39/0.60  thf('83', plain, ($false),
% 0.39/0.60      inference('demod', [status(thm)], ['69', '80', '81', '82'])).
% 0.39/0.60  
% 0.39/0.60  % SZS output end Refutation
% 0.39/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
