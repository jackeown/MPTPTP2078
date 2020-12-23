%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iNd4RbtGwd

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:32 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 191 expanded)
%              Number of leaves         :   28 (  68 expanded)
%              Depth                    :   20
%              Number of atoms          :  749 (3622 expanded)
%              Number of equality atoms :   11 (  80 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t57_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v2_tex_2 @ X15 @ X16 )
      | ( r2_hidden @ ( sk_C @ X15 @ X16 ) @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v3_tdlat_3 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t57_tex_2])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('18',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X13 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['10','11'])).

thf('30',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ X18 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X18 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('32',plain,(
    ! [X18: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X18 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X18 ) )
      | ~ ( r2_hidden @ X18 @ sk_B ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v2_tex_2 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X16 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 @ X17 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X16 ) @ ( sk_C @ X15 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v3_tdlat_3 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t57_tex_2])).

thf('35',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('41',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('51',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('52',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('54',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['50','51'])).

thf('57',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['0','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iNd4RbtGwd
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:01:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.36/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.59  % Solved by: fo/fo7.sh
% 0.36/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.59  % done 322 iterations in 0.175s
% 0.36/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.59  % SZS output start Refutation
% 0.36/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.59  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.36/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.59  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.36/0.59  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.36/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.36/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.59  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.36/0.59  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.36/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.36/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.59  thf(t58_tex_2, conjecture,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.36/0.59         ( l1_pre_topc @ A ) ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.59           ( ( ![C:$i]:
% 0.36/0.59               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.59                 ( ( r2_hidden @ C @ B ) =>
% 0.36/0.59                   ( ( k9_subset_1 @
% 0.36/0.59                       ( u1_struct_0 @ A ) @ B @ 
% 0.36/0.59                       ( k2_pre_topc @
% 0.36/0.59                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.36/0.59                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.36/0.59             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.36/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.59    (~( ![A:$i]:
% 0.36/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.59            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.59          ( ![B:$i]:
% 0.36/0.59            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.59              ( ( ![C:$i]:
% 0.36/0.59                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.59                    ( ( r2_hidden @ C @ B ) =>
% 0.36/0.59                      ( ( k9_subset_1 @
% 0.36/0.59                          ( u1_struct_0 @ A ) @ B @ 
% 0.36/0.59                          ( k2_pre_topc @
% 0.36/0.59                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.36/0.59                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) =>
% 0.36/0.59                ( v2_tex_2 @ B @ A ) ) ) ) ) )),
% 0.36/0.59    inference('cnf.neg', [status(esa)], [t58_tex_2])).
% 0.36/0.59  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(d3_struct_0, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.36/0.59  thf('1', plain,
% 0.36/0.59      (![X6 : $i]:
% 0.36/0.59         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.36/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.59  thf('2', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(t57_tex_2, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.36/0.59         ( l1_pre_topc @ A ) ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.59           ( ( ![C:$i]:
% 0.36/0.59               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.59                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.36/0.59                      ( ![D:$i]:
% 0.36/0.59                        ( ( m1_subset_1 @
% 0.36/0.59                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.59                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.36/0.59                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.36/0.59                                 ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) ) =>
% 0.36/0.59             ( v2_tex_2 @ B @ A ) ) ) ) ))).
% 0.36/0.59  thf('3', plain,
% 0.36/0.59      (![X15 : $i, X16 : $i]:
% 0.36/0.59         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.59          | (v2_tex_2 @ X15 @ X16)
% 0.36/0.59          | (r2_hidden @ (sk_C @ X15 @ X16) @ X15)
% 0.36/0.59          | ~ (l1_pre_topc @ X16)
% 0.36/0.59          | ~ (v3_tdlat_3 @ X16)
% 0.36/0.59          | ~ (v2_pre_topc @ X16)
% 0.36/0.59          | (v2_struct_0 @ X16))),
% 0.36/0.59      inference('cnf', [status(esa)], [t57_tex_2])).
% 0.36/0.59  thf('4', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.59        | ~ (v3_tdlat_3 @ sk_A)
% 0.36/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.59        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.36/0.59        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.59  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('6', plain, ((v3_tdlat_3 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('8', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)
% 0.36/0.59        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.36/0.59  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('10', plain,
% 0.36/0.59      (((v2_tex_2 @ sk_B @ sk_A) | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.36/0.59      inference('clc', [status(thm)], ['8', '9'])).
% 0.36/0.59  thf('11', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('12', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.36/0.59      inference('clc', [status(thm)], ['10', '11'])).
% 0.36/0.59  thf('13', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(t4_subset, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.36/0.59       ( m1_subset_1 @ A @ C ) ))).
% 0.36/0.59  thf('14', plain,
% 0.36/0.59      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X3 @ X4)
% 0.36/0.59          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.36/0.59          | (m1_subset_1 @ X3 @ X5))),
% 0.36/0.59      inference('cnf', [status(esa)], [t4_subset])).
% 0.36/0.59  thf('15', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.36/0.59      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.59  thf('16', plain,
% 0.36/0.59      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['12', '15'])).
% 0.36/0.59  thf(dt_k6_domain_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.36/0.59       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.59  thf('17', plain,
% 0.36/0.59      (![X11 : $i, X12 : $i]:
% 0.36/0.59         ((v1_xboole_0 @ X11)
% 0.36/0.59          | ~ (m1_subset_1 @ X12 @ X11)
% 0.36/0.59          | (m1_subset_1 @ (k6_domain_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11)))),
% 0.36/0.59      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.36/0.59  thf('18', plain,
% 0.36/0.59      (((m1_subset_1 @ 
% 0.36/0.59         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)) @ 
% 0.36/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.59  thf(fc1_tops_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.36/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.59       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.36/0.59  thf('19', plain,
% 0.36/0.59      (![X13 : $i, X14 : $i]:
% 0.36/0.59         (~ (l1_pre_topc @ X13)
% 0.36/0.59          | ~ (v2_pre_topc @ X13)
% 0.36/0.59          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.36/0.59          | (v4_pre_topc @ (k2_pre_topc @ X13 @ X14) @ X13))),
% 0.36/0.59      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.36/0.59  thf('20', plain,
% 0.36/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.59        | (v4_pre_topc @ 
% 0.36/0.59           (k2_pre_topc @ sk_A @ 
% 0.36/0.59            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.36/0.59           sk_A)
% 0.36/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.59  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('23', plain,
% 0.36/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.59        | (v4_pre_topc @ 
% 0.36/0.59           (k2_pre_topc @ sk_A @ 
% 0.36/0.59            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.36/0.59           sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.36/0.59  thf('24', plain,
% 0.36/0.59      (((m1_subset_1 @ 
% 0.36/0.59         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)) @ 
% 0.36/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.59  thf(dt_k2_pre_topc, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ( l1_pre_topc @ A ) & 
% 0.36/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.59       ( m1_subset_1 @
% 0.36/0.59         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.59  thf('25', plain,
% 0.36/0.59      (![X7 : $i, X8 : $i]:
% 0.36/0.59         (~ (l1_pre_topc @ X7)
% 0.36/0.59          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.36/0.59          | (m1_subset_1 @ (k2_pre_topc @ X7 @ X8) @ 
% 0.36/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.36/0.59      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.36/0.59  thf('26', plain,
% 0.36/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.59        | (m1_subset_1 @ 
% 0.36/0.59           (k2_pre_topc @ sk_A @ 
% 0.36/0.59            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.36/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.59  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('28', plain,
% 0.36/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.59        | (m1_subset_1 @ 
% 0.36/0.59           (k2_pre_topc @ sk_A @ 
% 0.36/0.59            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.36/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.59  thf('29', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.36/0.59      inference('clc', [status(thm)], ['10', '11'])).
% 0.36/0.59  thf('30', plain,
% 0.36/0.59      (![X18 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X18 @ sk_B)
% 0.36/0.59          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.59              (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X18)))
% 0.36/0.59              = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X18))
% 0.36/0.59          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('31', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.36/0.59      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.59  thf('32', plain,
% 0.36/0.59      (![X18 : $i]:
% 0.36/0.59         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.59            (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X18)))
% 0.36/0.59            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X18))
% 0.36/0.59          | ~ (r2_hidden @ X18 @ sk_B))),
% 0.36/0.59      inference('clc', [status(thm)], ['30', '31'])).
% 0.36/0.59  thf('33', plain,
% 0.36/0.59      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.59         (k2_pre_topc @ sk_A @ 
% 0.36/0.59          (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))))
% 0.36/0.59         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['29', '32'])).
% 0.36/0.59  thf('34', plain,
% 0.36/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.59         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.59          | (v2_tex_2 @ X15 @ X16)
% 0.36/0.59          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.59          | ~ (v4_pre_topc @ X17 @ X16)
% 0.36/0.59          | ((k9_subset_1 @ (u1_struct_0 @ X16) @ X15 @ X17)
% 0.36/0.59              != (k6_domain_1 @ (u1_struct_0 @ X16) @ (sk_C @ X15 @ X16)))
% 0.36/0.59          | ~ (l1_pre_topc @ X16)
% 0.36/0.59          | ~ (v3_tdlat_3 @ X16)
% 0.36/0.59          | ~ (v2_pre_topc @ X16)
% 0.36/0.59          | (v2_struct_0 @ X16))),
% 0.36/0.59      inference('cnf', [status(esa)], [t57_tex_2])).
% 0.36/0.59  thf('35', plain,
% 0.36/0.59      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))
% 0.36/0.59          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)))
% 0.36/0.59        | (v2_struct_0 @ sk_A)
% 0.36/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.59        | ~ (v3_tdlat_3 @ sk_A)
% 0.36/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.59        | ~ (v4_pre_topc @ 
% 0.36/0.59             (k2_pre_topc @ sk_A @ 
% 0.36/0.59              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.36/0.59             sk_A)
% 0.36/0.59        | ~ (m1_subset_1 @ 
% 0.36/0.59             (k2_pre_topc @ sk_A @ 
% 0.36/0.59              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.36/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.59        | (v2_tex_2 @ sk_B @ sk_A)
% 0.36/0.59        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.59  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('37', plain, ((v3_tdlat_3 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('39', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('40', plain,
% 0.36/0.59      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))
% 0.36/0.59          != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A)))
% 0.36/0.59        | (v2_struct_0 @ sk_A)
% 0.36/0.59        | ~ (v4_pre_topc @ 
% 0.36/0.59             (k2_pre_topc @ sk_A @ 
% 0.36/0.59              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.36/0.59             sk_A)
% 0.36/0.59        | ~ (m1_subset_1 @ 
% 0.36/0.59             (k2_pre_topc @ sk_A @ 
% 0.36/0.59              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.36/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.59        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 0.36/0.59  thf('41', plain,
% 0.36/0.59      (((v2_tex_2 @ sk_B @ sk_A)
% 0.36/0.59        | ~ (m1_subset_1 @ 
% 0.36/0.59             (k2_pre_topc @ sk_A @ 
% 0.36/0.59              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.36/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.59        | ~ (v4_pre_topc @ 
% 0.36/0.59             (k2_pre_topc @ sk_A @ 
% 0.36/0.59              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.36/0.59             sk_A)
% 0.36/0.59        | (v2_struct_0 @ sk_A))),
% 0.36/0.59      inference('simplify', [status(thm)], ['40'])).
% 0.36/0.59  thf('42', plain,
% 0.36/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.59        | (v2_struct_0 @ sk_A)
% 0.36/0.59        | ~ (v4_pre_topc @ 
% 0.36/0.59             (k2_pre_topc @ sk_A @ 
% 0.36/0.59              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_C @ sk_B @ sk_A))) @ 
% 0.36/0.59             sk_A)
% 0.36/0.59        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['28', '41'])).
% 0.36/0.59  thf('43', plain,
% 0.36/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.59        | (v2_tex_2 @ sk_B @ sk_A)
% 0.36/0.59        | (v2_struct_0 @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['23', '42'])).
% 0.36/0.59  thf('44', plain,
% 0.36/0.59      (((v2_struct_0 @ sk_A)
% 0.36/0.59        | (v2_tex_2 @ sk_B @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.36/0.59  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('46', plain,
% 0.36/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_tex_2 @ sk_B @ sk_A))),
% 0.36/0.59      inference('clc', [status(thm)], ['44', '45'])).
% 0.36/0.59  thf('47', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('48', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.36/0.59      inference('clc', [status(thm)], ['46', '47'])).
% 0.36/0.59  thf('49', plain,
% 0.36/0.59      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.59      inference('sup+', [status(thm)], ['1', '48'])).
% 0.36/0.59  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(dt_l1_pre_topc, axiom,
% 0.36/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.59  thf('51', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.36/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.59  thf('52', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.59  thf('53', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['49', '52'])).
% 0.36/0.59  thf(fc5_struct_0, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.59       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.36/0.59  thf('54', plain,
% 0.36/0.59      (![X10 : $i]:
% 0.36/0.59         (~ (v1_xboole_0 @ (k2_struct_0 @ X10))
% 0.36/0.59          | ~ (l1_struct_0 @ X10)
% 0.36/0.59          | (v2_struct_0 @ X10))),
% 0.36/0.59      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.36/0.59  thf('55', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['53', '54'])).
% 0.36/0.59  thf('56', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.59  thf('57', plain, ((v2_struct_0 @ sk_A)),
% 0.36/0.59      inference('demod', [status(thm)], ['55', '56'])).
% 0.36/0.59  thf('58', plain, ($false), inference('demod', [status(thm)], ['0', '57'])).
% 0.36/0.59  
% 0.36/0.59  % SZS output end Refutation
% 0.36/0.59  
% 0.36/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
