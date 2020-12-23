%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nj1sZR6Wb7

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:31 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 235 expanded)
%              Number of leaves         :   27 (  79 expanded)
%              Depth                    :   19
%              Number of atoms          :  896 (4654 expanded)
%              Number of equality atoms :    9 (  97 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t58_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                    = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ C @ B )
                   => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                      = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) )
             => ( v2_tex_2 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t58_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v2_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t35_tex_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v2_tex_2 @ X15 @ X16 )
      | ( r2_hidden @ ( sk_C @ X15 @ X16 ) @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( m1_subset_1 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_tdlat_3 @ X11 )
      | ~ ( v4_pre_topc @ X12 @ X11 )
      | ( v3_pre_topc @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X9 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('47',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['20','21'])).

thf('48',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ X18 @ sk_B_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X18 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('50',plain,(
    ! [X18: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X18 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X18 ) )
      | ~ ( r2_hidden @ X18 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v2_tex_2 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X16 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 @ X17 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X16 ) @ ( sk_C @ X15 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('53',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','59'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['12','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['9','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nj1sZR6Wb7
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 141 iterations in 0.139s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.46/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.64  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.46/0.64  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.64  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.64  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.64  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.46/0.64  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.46/0.64  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.46/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.64  thf(t58_tex_2, conjecture,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.46/0.64         ( l1_pre_topc @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.64           ( ( ![C:$i]:
% 0.46/0.64               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.64                 ( ( r2_hidden @ C @ B ) =>
% 0.46/0.64                   ( ( k9_subset_1 @
% 0.46/0.64                       ( u1_struct_0 @ A ) @ B @ 
% 0.46/0.64                       ( k2_pre_topc @
% 0.46/0.64                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.46/0.64                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.46/0.64             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i]:
% 0.46/0.64        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.64            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.64          ( ![B:$i]:
% 0.46/0.64            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.64              ( ( ![C:$i]:
% 0.46/0.64                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.64                    ( ( r2_hidden @ C @ B ) =>
% 0.46/0.64                      ( ( k9_subset_1 @
% 0.46/0.64                          ( u1_struct_0 @ A ) @ B @ 
% 0.46/0.64                          ( k2_pre_topc @
% 0.46/0.64                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.46/0.64                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.46/0.64                ( v2_tex_2 @ B @ A ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t58_tex_2])).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t35_tex_2, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( v1_xboole_0 @ B ) & 
% 0.46/0.64             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.64           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         (~ (v1_xboole_0 @ X13)
% 0.46/0.64          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.46/0.64          | (v2_tex_2 @ X13 @ X14)
% 0.46/0.64          | ~ (l1_pre_topc @ X14)
% 0.46/0.64          | ~ (v2_pre_topc @ X14)
% 0.46/0.64          | (v2_struct_0 @ X14))),
% 0.46/0.64      inference('cnf', [status(esa)], [t35_tex_2])).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A)
% 0.46/0.64        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.64        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.64        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.46/0.64        | ~ (v1_xboole_0 @ sk_B_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.64  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A)
% 0.46/0.64        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.46/0.64        | ~ (v1_xboole_0 @ sk_B_1))),
% 0.46/0.64      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.46/0.64  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('7', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.46/0.64      inference('clc', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('8', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('9', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.46/0.64      inference('clc', [status(thm)], ['7', '8'])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(cc1_subset_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_xboole_0 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.64          | (v1_xboole_0 @ X0)
% 0.46/0.64          | ~ (v1_xboole_0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t37_tex_2, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.64           ( ( ![C:$i]:
% 0.46/0.64               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.64                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.46/0.64                      ( ![D:$i]:
% 0.46/0.64                        ( ( m1_subset_1 @
% 0.46/0.64                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.64                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.46/0.64                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.46/0.64                                 ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) ) =>
% 0.46/0.64             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.46/0.64          | (v2_tex_2 @ X15 @ X16)
% 0.46/0.64          | (r2_hidden @ (sk_C @ X15 @ X16) @ X15)
% 0.46/0.64          | ~ (l1_pre_topc @ X16)
% 0.46/0.65          | ~ (v2_pre_topc @ X16)
% 0.46/0.65          | (v2_struct_0 @ X16))),
% 0.46/0.65      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_A)
% 0.46/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65        | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.46/0.65        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.65  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_A)
% 0.46/0.65        | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.46/0.65        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.46/0.65  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.46/0.65        | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.46/0.65      inference('clc', [status(thm)], ['18', '19'])).
% 0.46/0.65  thf('21', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('22', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.46/0.65      inference('clc', [status(thm)], ['20', '21'])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t4_subset, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.46/0.65       ( m1_subset_1 @ A @ C ) ))).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X2 @ X3)
% 0.46/0.65          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.46/0.65          | (m1_subset_1 @ X2 @ X4))),
% 0.46/0.65      inference('cnf', [status(esa)], [t4_subset])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      ((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['22', '25'])).
% 0.46/0.65  thf(dt_k6_domain_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.46/0.65       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (![X7 : $i, X8 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X7)
% 0.46/0.65          | ~ (m1_subset_1 @ X8 @ X7)
% 0.46/0.65          | (m1_subset_1 @ (k6_domain_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (((m1_subset_1 @ 
% 0.46/0.65         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)) @ 
% 0.46/0.65         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.65  thf(dt_k2_pre_topc, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( l1_pre_topc @ A ) & 
% 0.46/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.65       ( m1_subset_1 @
% 0.46/0.65         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X5 : $i, X6 : $i]:
% 0.46/0.65         (~ (l1_pre_topc @ X5)
% 0.46/0.65          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.46/0.65          | (m1_subset_1 @ (k2_pre_topc @ X5 @ X6) @ 
% 0.46/0.65             (k1_zfmisc_1 @ (u1_struct_0 @ X5))))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (m1_subset_1 @ 
% 0.46/0.65           (k2_pre_topc @ sk_A @ 
% 0.46/0.65            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.65  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (m1_subset_1 @ 
% 0.46/0.65           (k2_pre_topc @ sk_A @ 
% 0.46/0.65            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.65  thf(t24_tdlat_3, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.65       ( ( v3_tdlat_3 @ A ) <=>
% 0.46/0.65         ( ![B:$i]:
% 0.46/0.65           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i]:
% 0.46/0.65         (~ (v3_tdlat_3 @ X11)
% 0.46/0.65          | ~ (v4_pre_topc @ X12 @ X11)
% 0.46/0.65          | (v3_pre_topc @ X12 @ X11)
% 0.46/0.65          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.46/0.65          | ~ (l1_pre_topc @ X11)
% 0.46/0.65          | ~ (v2_pre_topc @ X11))),
% 0.46/0.65      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65        | (v3_pre_topc @ 
% 0.46/0.65           (k2_pre_topc @ sk_A @ 
% 0.46/0.65            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.46/0.65           sk_A)
% 0.46/0.65        | ~ (v4_pre_topc @ 
% 0.46/0.65             (k2_pre_topc @ sk_A @ 
% 0.46/0.65              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.46/0.65             sk_A)
% 0.46/0.65        | ~ (v3_tdlat_3 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.65  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('37', plain, ((v3_tdlat_3 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v3_pre_topc @ 
% 0.46/0.65           (k2_pre_topc @ sk_A @ 
% 0.46/0.65            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.46/0.65           sk_A)
% 0.46/0.65        | ~ (v4_pre_topc @ 
% 0.46/0.65             (k2_pre_topc @ sk_A @ 
% 0.46/0.65              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.46/0.65             sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (((m1_subset_1 @ 
% 0.46/0.65         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)) @ 
% 0.46/0.65         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.65  thf(fc1_tops_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.46/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.65       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      (![X9 : $i, X10 : $i]:
% 0.46/0.65         (~ (l1_pre_topc @ X9)
% 0.46/0.65          | ~ (v2_pre_topc @ X9)
% 0.46/0.65          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.46/0.65          | (v4_pre_topc @ (k2_pre_topc @ X9 @ X10) @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v4_pre_topc @ 
% 0.46/0.65           (k2_pre_topc @ sk_A @ 
% 0.46/0.65            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.46/0.65           sk_A)
% 0.46/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.65  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v4_pre_topc @ 
% 0.46/0.65           (k2_pre_topc @ sk_A @ 
% 0.46/0.65            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.46/0.65           sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      (((v3_pre_topc @ 
% 0.46/0.65         (k2_pre_topc @ sk_A @ 
% 0.46/0.65          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.46/0.65         sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('clc', [status(thm)], ['38', '44'])).
% 0.46/0.65  thf('46', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (m1_subset_1 @ 
% 0.46/0.65           (k2_pre_topc @ sk_A @ 
% 0.46/0.65            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.65  thf('47', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.46/0.65      inference('clc', [status(thm)], ['20', '21'])).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      (![X18 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X18 @ sk_B_1)
% 0.46/0.65          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.46/0.65              (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X18)))
% 0.46/0.65              = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X18))
% 0.46/0.65          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf('50', plain,
% 0.46/0.65      (![X18 : $i]:
% 0.46/0.65         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.46/0.65            (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X18)))
% 0.46/0.65            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X18))
% 0.46/0.65          | ~ (r2_hidden @ X18 @ sk_B_1))),
% 0.46/0.65      inference('clc', [status(thm)], ['48', '49'])).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.46/0.65         (k2_pre_topc @ sk_A @ 
% 0.46/0.65          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))))
% 0.46/0.65         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['47', '50'])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.46/0.65          | (v2_tex_2 @ X15 @ X16)
% 0.46/0.65          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.46/0.65          | ~ (v3_pre_topc @ X17 @ X16)
% 0.46/0.65          | ((k9_subset_1 @ (u1_struct_0 @ X16) @ X15 @ X17)
% 0.46/0.65              != (k6_domain_1 @ (u1_struct_0 @ X16) @ (sk_C @ X15 @ X16)))
% 0.46/0.65          | ~ (l1_pre_topc @ X16)
% 0.46/0.65          | ~ (v2_pre_topc @ X16)
% 0.46/0.65          | (v2_struct_0 @ X16))),
% 0.46/0.65      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))
% 0.46/0.65          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65        | ~ (v3_pre_topc @ 
% 0.46/0.65             (k2_pre_topc @ sk_A @ 
% 0.46/0.65              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.46/0.65             sk_A)
% 0.46/0.65        | ~ (m1_subset_1 @ 
% 0.46/0.65             (k2_pre_topc @ sk_A @ 
% 0.46/0.65              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.46/0.65             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.46/0.65        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.65  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))
% 0.46/0.65          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A)))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | ~ (v3_pre_topc @ 
% 0.46/0.65             (k2_pre_topc @ sk_A @ 
% 0.46/0.65              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.46/0.65             sk_A)
% 0.46/0.65        | ~ (m1_subset_1 @ 
% 0.46/0.65             (k2_pre_topc @ sk_A @ 
% 0.46/0.65              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.46/0.65             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.46/0.65        | ~ (m1_subset_1 @ 
% 0.46/0.65             (k2_pre_topc @ sk_A @ 
% 0.46/0.65              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.46/0.65             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65        | ~ (v3_pre_topc @ 
% 0.46/0.65             (k2_pre_topc @ sk_A @ 
% 0.46/0.65              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.46/0.65             sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_A))),
% 0.46/0.65      inference('simplify', [status(thm)], ['57'])).
% 0.46/0.65  thf('59', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | ~ (v3_pre_topc @ 
% 0.46/0.65             (k2_pre_topc @ sk_A @ 
% 0.46/0.65              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.46/0.65             sk_A)
% 0.46/0.65        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['46', '58'])).
% 0.46/0.65  thf('60', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['45', '59'])).
% 0.46/0.65  thf('61', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_A)
% 0.46/0.65        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['60'])).
% 0.46/0.65  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('63', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('clc', [status(thm)], ['61', '62'])).
% 0.46/0.65  thf('64', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('65', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('clc', [status(thm)], ['63', '64'])).
% 0.46/0.65  thf('66', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.46/0.65      inference('demod', [status(thm)], ['12', '65'])).
% 0.46/0.65  thf('67', plain, ($false), inference('demod', [status(thm)], ['9', '66'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
