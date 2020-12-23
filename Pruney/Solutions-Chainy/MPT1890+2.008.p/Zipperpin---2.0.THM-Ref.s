%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.k8V4tql9zO

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:32 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 302 expanded)
%              Number of leaves         :   28 ( 100 expanded)
%              Depth                    :   17
%              Number of atoms          :  781 (5955 expanded)
%              Number of equality atoms :    9 ( 127 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_tex_2 @ X18 @ X19 )
      | ( m1_subset_1 @ ( sk_C_1 @ X18 @ X19 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X21: $i] :
      ( ~ ( r2_hidden @ X21 @ sk_B_2 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X21 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_tex_2 @ X18 @ X19 )
      | ( r2_hidden @ ( sk_C_1 @ X18 @ X19 ) @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_B_2 )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_B_2 )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_B_2 ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_B_2 ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','22'])).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_tex_2 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X19 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 @ X20 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X19 ) @ ( sk_C_1 @ X18 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t37_tex_2])).

thf('25',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_B_2 ),
    inference(clc,[status(thm)],['20','21'])).

thf('32',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    r1_tarski @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','39'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('42',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_tdlat_3 @ X16 )
      | ~ ( v4_pre_topc @ X17 @ X16 )
      | ( v3_pre_topc @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('46',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','39'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X14 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('51',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['46','47','48','54','55'])).

thf('57',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('58',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27','56','57','58'])).

thf('60',plain,
    ( ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ~ ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['0','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.k8V4tql9zO
% 0.15/0.38  % Computer   : n003.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 13:57:42 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 181 iterations in 0.123s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.61  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.43/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.43/0.61  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.43/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.61  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.43/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.43/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.43/0.61  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.43/0.61  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.43/0.61  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.43/0.61  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.43/0.61  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.43/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.61  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.43/0.61  thf(t58_tex_2, conjecture,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.43/0.61         ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61           ( ( ![C:$i]:
% 0.43/0.61               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61                 ( ( r2_hidden @ C @ B ) =>
% 0.43/0.61                   ( ( k9_subset_1 @
% 0.43/0.61                       ( u1_struct_0 @ A ) @ B @ 
% 0.43/0.61                       ( k2_pre_topc @
% 0.43/0.61                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.43/0.61                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.43/0.61             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i]:
% 0.43/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.43/0.61            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61          ( ![B:$i]:
% 0.43/0.61            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61              ( ( ![C:$i]:
% 0.43/0.61                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61                    ( ( r2_hidden @ C @ B ) =>
% 0.43/0.61                      ( ( k9_subset_1 @
% 0.43/0.61                          ( u1_struct_0 @ A ) @ B @ 
% 0.43/0.61                          ( k2_pre_topc @
% 0.43/0.61                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.43/0.61                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.43/0.61                ( v2_tex_2 @ B @ A ) ) ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t58_tex_2])).
% 0.43/0.61  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t37_tex_2, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61           ( ( ![C:$i]:
% 0.43/0.61               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.43/0.61                      ( ![D:$i]:
% 0.43/0.61                        ( ( m1_subset_1 @
% 0.43/0.61                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.43/0.61                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.43/0.61                                 ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) ) =>
% 0.43/0.61             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.43/0.61          | (v2_tex_2 @ X18 @ X19)
% 0.43/0.61          | (m1_subset_1 @ (sk_C_1 @ X18 @ X19) @ (u1_struct_0 @ X19))
% 0.43/0.61          | ~ (l1_pre_topc @ X19)
% 0.43/0.61          | ~ (v2_pre_topc @ X19)
% 0.43/0.61          | (v2_struct_0 @ X19))),
% 0.43/0.61      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | (m1_subset_1 @ (sk_C_1 @ sk_B_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.43/0.61  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('6', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | (m1_subset_1 @ (sk_C_1 @ sk_B_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.43/0.61  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      (((v2_tex_2 @ sk_B_2 @ sk_A)
% 0.43/0.61        | (m1_subset_1 @ (sk_C_1 @ sk_B_2 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('clc', [status(thm)], ['6', '7'])).
% 0.43/0.61  thf('9', plain, (~ (v2_tex_2 @ sk_B_2 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      ((m1_subset_1 @ (sk_C_1 @ sk_B_2 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('clc', [status(thm)], ['8', '9'])).
% 0.43/0.61  thf('11', plain,
% 0.43/0.61      (![X21 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X21 @ sk_B_2)
% 0.43/0.61          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2 @ 
% 0.43/0.61              (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X21)))
% 0.43/0.61              = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X21))
% 0.43/0.61          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('12', plain,
% 0.43/0.61      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2 @ 
% 0.43/0.61          (k2_pre_topc @ sk_A @ 
% 0.43/0.61           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A))))
% 0.43/0.61          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 0.43/0.61        | ~ (r2_hidden @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_B_2))),
% 0.43/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.43/0.61  thf('13', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('14', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.43/0.61          | (v2_tex_2 @ X18 @ X19)
% 0.43/0.61          | (r2_hidden @ (sk_C_1 @ X18 @ X19) @ X18)
% 0.43/0.61          | ~ (l1_pre_topc @ X19)
% 0.43/0.61          | ~ (v2_pre_topc @ X19)
% 0.43/0.61          | (v2_struct_0 @ X19))),
% 0.43/0.61      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | (r2_hidden @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_B_2)
% 0.43/0.61        | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.43/0.61  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | (r2_hidden @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_B_2)
% 0.43/0.61        | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.43/0.61  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('20', plain,
% 0.43/0.61      (((v2_tex_2 @ sk_B_2 @ sk_A)
% 0.43/0.61        | (r2_hidden @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_B_2))),
% 0.43/0.61      inference('clc', [status(thm)], ['18', '19'])).
% 0.43/0.61  thf('21', plain, (~ (v2_tex_2 @ sk_B_2 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('22', plain, ((r2_hidden @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_B_2)),
% 0.43/0.61      inference('clc', [status(thm)], ['20', '21'])).
% 0.43/0.61  thf('23', plain,
% 0.43/0.61      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2 @ 
% 0.43/0.61         (k2_pre_topc @ sk_A @ 
% 0.43/0.61          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A))))
% 0.43/0.61         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['12', '22'])).
% 0.43/0.61  thf('24', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.43/0.61          | (v2_tex_2 @ X18 @ X19)
% 0.43/0.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.43/0.61          | ~ (v3_pre_topc @ X20 @ X19)
% 0.43/0.61          | ((k9_subset_1 @ (u1_struct_0 @ X19) @ X18 @ X20)
% 0.43/0.61              != (k6_domain_1 @ (u1_struct_0 @ X19) @ (sk_C_1 @ X18 @ X19)))
% 0.43/0.61          | ~ (l1_pre_topc @ X19)
% 0.43/0.61          | ~ (v2_pre_topc @ X19)
% 0.43/0.61          | (v2_struct_0 @ X19))),
% 0.43/0.61      inference('cnf', [status(esa)], [t37_tex_2])).
% 0.43/0.61  thf('25', plain,
% 0.43/0.61      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.43/0.61          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | ~ (v3_pre_topc @ 
% 0.43/0.61             (k2_pre_topc @ sk_A @ 
% 0.43/0.61              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A))) @ 
% 0.43/0.61             sk_A)
% 0.43/0.61        | ~ (m1_subset_1 @ 
% 0.43/0.61             (k2_pre_topc @ sk_A @ 
% 0.43/0.61              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A))) @ 
% 0.43/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61        | (v2_tex_2 @ sk_B_2 @ sk_A)
% 0.43/0.61        | ~ (m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['23', '24'])).
% 0.43/0.61  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('28', plain,
% 0.43/0.61      ((m1_subset_1 @ (sk_C_1 @ sk_B_2 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('clc', [status(thm)], ['8', '9'])).
% 0.43/0.61  thf(dt_k6_domain_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.43/0.61       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.43/0.61  thf('29', plain,
% 0.43/0.61      (![X12 : $i, X13 : $i]:
% 0.43/0.61         ((v1_xboole_0 @ X12)
% 0.43/0.61          | ~ (m1_subset_1 @ X13 @ X12)
% 0.43/0.61          | (m1_subset_1 @ (k6_domain_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12)))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.43/0.61  thf('30', plain,
% 0.43/0.61      (((m1_subset_1 @ 
% 0.43/0.61         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A)) @ 
% 0.43/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['28', '29'])).
% 0.43/0.61  thf('31', plain, ((r2_hidden @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_B_2)),
% 0.43/0.61      inference('clc', [status(thm)], ['20', '21'])).
% 0.43/0.61  thf('32', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t3_subset, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.43/0.61  thf('33', plain,
% 0.43/0.61      (![X7 : $i, X8 : $i]:
% 0.43/0.61         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.43/0.61  thf('34', plain, ((r1_tarski @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.43/0.61  thf(d3_tarski, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.43/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.43/0.61  thf('35', plain,
% 0.43/0.61      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X3 @ X4)
% 0.43/0.61          | (r2_hidden @ X3 @ X5)
% 0.43/0.61          | ~ (r1_tarski @ X4 @ X5))),
% 0.43/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.43/0.61  thf('36', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.43/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.43/0.61  thf('37', plain,
% 0.43/0.61      ((r2_hidden @ (sk_C_1 @ sk_B_2 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['31', '36'])).
% 0.43/0.61  thf(d1_xboole_0, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.43/0.61  thf('38', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.43/0.61  thf('39', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.43/0.61  thf('40', plain,
% 0.43/0.61      ((m1_subset_1 @ 
% 0.43/0.61        (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A)) @ 
% 0.43/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('clc', [status(thm)], ['30', '39'])).
% 0.43/0.61  thf(dt_k2_pre_topc, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( l1_pre_topc @ A ) & 
% 0.43/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.43/0.61       ( m1_subset_1 @
% 0.43/0.61         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.43/0.61  thf('41', plain,
% 0.43/0.61      (![X10 : $i, X11 : $i]:
% 0.43/0.61         (~ (l1_pre_topc @ X10)
% 0.43/0.61          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.43/0.61          | (m1_subset_1 @ (k2_pre_topc @ X10 @ X11) @ 
% 0.43/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.43/0.61  thf('42', plain,
% 0.43/0.61      (((m1_subset_1 @ 
% 0.43/0.61         (k2_pre_topc @ sk_A @ 
% 0.43/0.61          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A))) @ 
% 0.43/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.43/0.61  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('44', plain,
% 0.43/0.61      ((m1_subset_1 @ 
% 0.43/0.61        (k2_pre_topc @ sk_A @ 
% 0.43/0.61         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A))) @ 
% 0.43/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['42', '43'])).
% 0.43/0.61  thf(t24_tdlat_3, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( ( v3_tdlat_3 @ A ) <=>
% 0.43/0.61         ( ![B:$i]:
% 0.43/0.61           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.43/0.61  thf('45', plain,
% 0.43/0.61      (![X16 : $i, X17 : $i]:
% 0.43/0.61         (~ (v3_tdlat_3 @ X16)
% 0.43/0.61          | ~ (v4_pre_topc @ X17 @ X16)
% 0.43/0.61          | (v3_pre_topc @ X17 @ X16)
% 0.43/0.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.43/0.61          | ~ (l1_pre_topc @ X16)
% 0.43/0.61          | ~ (v2_pre_topc @ X16))),
% 0.43/0.61      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.43/0.61  thf('46', plain,
% 0.43/0.61      ((~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | (v3_pre_topc @ 
% 0.43/0.61           (k2_pre_topc @ sk_A @ 
% 0.43/0.61            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A))) @ 
% 0.43/0.61           sk_A)
% 0.43/0.61        | ~ (v4_pre_topc @ 
% 0.43/0.61             (k2_pre_topc @ sk_A @ 
% 0.43/0.61              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A))) @ 
% 0.43/0.61             sk_A)
% 0.43/0.61        | ~ (v3_tdlat_3 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.43/0.61  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('49', plain,
% 0.43/0.61      ((m1_subset_1 @ 
% 0.43/0.61        (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A)) @ 
% 0.43/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('clc', [status(thm)], ['30', '39'])).
% 0.43/0.61  thf(fc1_tops_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.43/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.43/0.61       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.43/0.61  thf('50', plain,
% 0.43/0.61      (![X14 : $i, X15 : $i]:
% 0.43/0.61         (~ (l1_pre_topc @ X14)
% 0.43/0.61          | ~ (v2_pre_topc @ X14)
% 0.43/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.43/0.61          | (v4_pre_topc @ (k2_pre_topc @ X14 @ X15) @ X14))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.43/0.61  thf('51', plain,
% 0.43/0.61      (((v4_pre_topc @ 
% 0.43/0.61         (k2_pre_topc @ sk_A @ 
% 0.43/0.61          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A))) @ 
% 0.43/0.61         sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['49', '50'])).
% 0.43/0.61  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('54', plain,
% 0.43/0.61      ((v4_pre_topc @ 
% 0.43/0.61        (k2_pre_topc @ sk_A @ 
% 0.43/0.61         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A))) @ 
% 0.43/0.61        sk_A)),
% 0.43/0.61      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.43/0.61  thf('55', plain, ((v3_tdlat_3 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('56', plain,
% 0.43/0.61      ((v3_pre_topc @ 
% 0.43/0.61        (k2_pre_topc @ sk_A @ 
% 0.43/0.61         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A))) @ 
% 0.43/0.61        sk_A)),
% 0.43/0.61      inference('demod', [status(thm)], ['46', '47', '48', '54', '55'])).
% 0.43/0.61  thf('57', plain,
% 0.43/0.61      ((m1_subset_1 @ 
% 0.43/0.61        (k2_pre_topc @ sk_A @ 
% 0.43/0.61         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A))) @ 
% 0.43/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['42', '43'])).
% 0.43/0.61  thf('58', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('59', plain,
% 0.43/0.61      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.43/0.61          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['25', '26', '27', '56', '57', '58'])).
% 0.43/0.61  thf('60', plain, (((v2_tex_2 @ sk_B_2 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('simplify', [status(thm)], ['59'])).
% 0.43/0.61  thf('61', plain, (~ (v2_tex_2 @ sk_B_2 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('62', plain, ((v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('clc', [status(thm)], ['60', '61'])).
% 0.43/0.61  thf('63', plain, ($false), inference('demod', [status(thm)], ['0', '62'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
