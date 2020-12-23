%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sVeU3169yF

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:12 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 341 expanded)
%              Number of leaves         :   43 ( 111 expanded)
%              Depth                    :   20
%              Number of atoms          : 1298 (4045 expanded)
%              Number of equality atoms :   41 (  55 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t49_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tex_2 @ B @ A )
            <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_tex_2])).

thf('0',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ? [C: $i] :
              ( ( B
                = ( u1_struct_0 @ C ) )
              & ( m1_pre_topc @ C @ A )
              & ( v1_pre_topc @ C )
              & ~ ( v2_struct_0 @ C ) ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( X19
        = ( u1_struct_0 @ ( sk_C @ X19 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_pre_topc @ ( sk_C @ X19 @ X20 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('18',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t11_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_borsuk_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v4_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( X9
       != ( u1_struct_0 @ X7 ) )
      | ~ ( v1_borsuk_1 @ X7 @ X8 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v4_pre_topc @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_tsep_1])).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X7 ) @ X8 )
      | ~ ( v1_borsuk_1 @ X7 @ X8 )
      | ~ ( m1_pre_topc @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v1_borsuk_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v1_borsuk_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ sk_A )
    | ~ ( v1_borsuk_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf('28',plain,
    ( ~ ( v1_borsuk_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(cc5_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_borsuk_1 @ B @ A )
            & ( v1_tsep_1 @ B @ A )
            & ( v1_tdlat_3 @ B ) ) ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v1_borsuk_1 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v1_tdlat_3 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc5_tdlat_3])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_borsuk_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_borsuk_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_borsuk_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['28','37'])).

thf('39',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['8','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v4_pre_topc @ X4 @ X5 )
      | ( ( k2_pre_topc @ X5 @ X4 )
        = X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v3_tex_2 @ B @ A ) )
           => ( v1_tops_1 @ B @ A ) ) ) ) )).

thf('50',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v1_tops_1 @ X27 @ X28 )
      | ~ ( v3_tex_2 @ X27 @ X28 )
      | ~ ( v3_pre_topc @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('55',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_tdlat_3 @ X21 )
      | ( v3_pre_topc @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('56',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','53','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('66',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v1_tops_1 @ X15 @ X16 )
      | ( ( k2_pre_topc @ X16 @ X15 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['46','70'])).

thf('72',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['47'])).

thf('73',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf('74',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v3_tex_2 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','80'])).

thf('82',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['71','81'])).

thf('83',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('85',plain,(
    ! [X1: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X1 ) @ X1 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('87',plain,(
    ! [X1: $i] :
      ~ ( v1_subset_1 @ X1 @ X1 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['47'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('90',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('92',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18 = X17 )
      | ( v1_subset_1 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('93',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['47'])).

thf('95',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( sk_B_1
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['90','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('98',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('99',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( sk_B_1
      = ( k2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','99'])).

thf(t27_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('101',plain,(
    ! [X6: $i] :
      ( ( ( k2_pre_topc @ X6 @ ( k2_struct_0 @ X6 ) )
        = ( k2_struct_0 @ X6 ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t27_tops_1])).

thf('102',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( sk_B_1
      = ( k2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','99'])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_pre_topc @ X16 @ X15 )
       != ( u1_struct_0 @ X16 ) )
      | ( v1_tops_1 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('108',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( sk_B_1
       != ( u1_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','110'])).

thf('112',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('113',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v1_tops_1 @ B @ A )
              & ( v2_tex_2 @ B @ A ) )
           => ( v3_tex_2 @ B @ A ) ) ) ) )).

thf('116',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v3_tex_2 @ X29 @ X30 )
      | ~ ( v2_tex_2 @ X29 @ X30 )
      | ~ ( v1_tops_1 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('121',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v1_tdlat_3 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['122','123','124','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['117','118','119','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','131'])).

thf('133',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('134',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','88','89','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sVeU3169yF
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:25:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 2.13/2.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.13/2.34  % Solved by: fo/fo7.sh
% 2.13/2.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.13/2.34  % done 1103 iterations in 1.850s
% 2.13/2.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.13/2.34  % SZS output start Refutation
% 2.13/2.34  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.13/2.34  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 2.13/2.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.13/2.34  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 2.13/2.34  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.13/2.34  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.13/2.34  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 2.13/2.34  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.13/2.34  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 2.13/2.34  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 2.13/2.34  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 2.13/2.34  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.13/2.34  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.13/2.34  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.13/2.34  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 2.13/2.34  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 2.13/2.34  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.13/2.34  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 2.13/2.34  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.13/2.34  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 2.13/2.34  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 2.13/2.34  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.13/2.34  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.13/2.34  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 2.13/2.34  thf(sk_A_type, type, sk_A: $i).
% 2.13/2.34  thf(t49_tex_2, conjecture,
% 2.13/2.34    (![A:$i]:
% 2.13/2.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 2.13/2.34         ( l1_pre_topc @ A ) ) =>
% 2.13/2.34       ( ![B:$i]:
% 2.13/2.34         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.13/2.34           ( ( v3_tex_2 @ B @ A ) <=>
% 2.13/2.34             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 2.13/2.34  thf(zf_stmt_0, negated_conjecture,
% 2.13/2.34    (~( ![A:$i]:
% 2.13/2.34        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.13/2.34            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.13/2.34          ( ![B:$i]:
% 2.13/2.34            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.13/2.34              ( ( v3_tex_2 @ B @ A ) <=>
% 2.13/2.34                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 2.13/2.34    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 2.13/2.34  thf('0', plain,
% 2.13/2.34      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 2.13/2.34        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('1', plain,
% 2.13/2.34      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 2.13/2.34       ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 2.13/2.34      inference('split', [status(esa)], ['0'])).
% 2.13/2.34  thf('2', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf(t10_tsep_1, axiom,
% 2.13/2.34    (![A:$i]:
% 2.13/2.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 2.13/2.34       ( ![B:$i]:
% 2.13/2.34         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 2.13/2.34             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.13/2.34           ( ?[C:$i]:
% 2.13/2.34             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 2.13/2.34               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 2.13/2.34  thf('3', plain,
% 2.13/2.34      (![X19 : $i, X20 : $i]:
% 2.13/2.34         ((v1_xboole_0 @ X19)
% 2.13/2.34          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.13/2.34          | ((X19) = (u1_struct_0 @ (sk_C @ X19 @ X20)))
% 2.13/2.34          | ~ (l1_pre_topc @ X20)
% 2.13/2.34          | (v2_struct_0 @ X20))),
% 2.13/2.34      inference('cnf', [status(esa)], [t10_tsep_1])).
% 2.13/2.34  thf('4', plain,
% 2.13/2.34      (((v2_struct_0 @ sk_A)
% 2.13/2.34        | ~ (l1_pre_topc @ sk_A)
% 2.13/2.34        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 2.13/2.34        | (v1_xboole_0 @ sk_B_1))),
% 2.13/2.34      inference('sup-', [status(thm)], ['2', '3'])).
% 2.13/2.34  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('6', plain,
% 2.13/2.34      (((v2_struct_0 @ sk_A)
% 2.13/2.34        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 2.13/2.34        | (v1_xboole_0 @ sk_B_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['4', '5'])).
% 2.13/2.34  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('8', plain,
% 2.13/2.34      (((v1_xboole_0 @ sk_B_1)
% 2.13/2.34        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))),
% 2.13/2.34      inference('clc', [status(thm)], ['6', '7'])).
% 2.13/2.34  thf('9', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('10', plain,
% 2.13/2.34      (![X19 : $i, X20 : $i]:
% 2.13/2.34         ((v1_xboole_0 @ X19)
% 2.13/2.34          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.13/2.34          | (m1_pre_topc @ (sk_C @ X19 @ X20) @ X20)
% 2.13/2.34          | ~ (l1_pre_topc @ X20)
% 2.13/2.34          | (v2_struct_0 @ X20))),
% 2.13/2.34      inference('cnf', [status(esa)], [t10_tsep_1])).
% 2.13/2.34  thf('11', plain,
% 2.13/2.34      (((v2_struct_0 @ sk_A)
% 2.13/2.34        | ~ (l1_pre_topc @ sk_A)
% 2.13/2.34        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 2.13/2.34        | (v1_xboole_0 @ sk_B_1))),
% 2.13/2.34      inference('sup-', [status(thm)], ['9', '10'])).
% 2.13/2.34  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('13', plain,
% 2.13/2.34      (((v2_struct_0 @ sk_A)
% 2.13/2.34        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 2.13/2.34        | (v1_xboole_0 @ sk_B_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['11', '12'])).
% 2.13/2.34  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('15', plain,
% 2.13/2.34      (((v1_xboole_0 @ sk_B_1) | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 2.13/2.34      inference('clc', [status(thm)], ['13', '14'])).
% 2.13/2.34  thf('16', plain,
% 2.13/2.34      (((v1_xboole_0 @ sk_B_1) | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 2.13/2.34      inference('clc', [status(thm)], ['13', '14'])).
% 2.13/2.34  thf(t1_tsep_1, axiom,
% 2.13/2.34    (![A:$i]:
% 2.13/2.34     ( ( l1_pre_topc @ A ) =>
% 2.13/2.34       ( ![B:$i]:
% 2.13/2.34         ( ( m1_pre_topc @ B @ A ) =>
% 2.13/2.34           ( m1_subset_1 @
% 2.13/2.34             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 2.13/2.34  thf('17', plain,
% 2.13/2.34      (![X10 : $i, X11 : $i]:
% 2.13/2.34         (~ (m1_pre_topc @ X10 @ X11)
% 2.13/2.34          | (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 2.13/2.34             (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 2.13/2.34          | ~ (l1_pre_topc @ X11))),
% 2.13/2.34      inference('cnf', [status(esa)], [t1_tsep_1])).
% 2.13/2.34  thf('18', plain,
% 2.13/2.34      (((v1_xboole_0 @ sk_B_1)
% 2.13/2.34        | ~ (l1_pre_topc @ sk_A)
% 2.13/2.34        | (m1_subset_1 @ (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)) @ 
% 2.13/2.34           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.13/2.34      inference('sup-', [status(thm)], ['16', '17'])).
% 2.13/2.34  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('20', plain,
% 2.13/2.34      (((v1_xboole_0 @ sk_B_1)
% 2.13/2.34        | (m1_subset_1 @ (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)) @ 
% 2.13/2.34           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.13/2.34      inference('demod', [status(thm)], ['18', '19'])).
% 2.13/2.34  thf(t11_tsep_1, axiom,
% 2.13/2.34    (![A:$i]:
% 2.13/2.34     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.13/2.34       ( ![B:$i]:
% 2.13/2.34         ( ( m1_pre_topc @ B @ A ) =>
% 2.13/2.34           ( ![C:$i]:
% 2.13/2.34             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.13/2.34               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 2.13/2.34                 ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 2.13/2.34                   ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 2.13/2.34  thf('21', plain,
% 2.13/2.34      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.13/2.34         (~ (m1_pre_topc @ X7 @ X8)
% 2.13/2.34          | ((X9) != (u1_struct_0 @ X7))
% 2.13/2.34          | ~ (v1_borsuk_1 @ X7 @ X8)
% 2.13/2.34          | ~ (m1_pre_topc @ X7 @ X8)
% 2.13/2.34          | (v4_pre_topc @ X9 @ X8)
% 2.13/2.34          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 2.13/2.34          | ~ (l1_pre_topc @ X8)
% 2.13/2.34          | ~ (v2_pre_topc @ X8))),
% 2.13/2.34      inference('cnf', [status(esa)], [t11_tsep_1])).
% 2.13/2.34  thf('22', plain,
% 2.13/2.34      (![X7 : $i, X8 : $i]:
% 2.13/2.34         (~ (v2_pre_topc @ X8)
% 2.13/2.34          | ~ (l1_pre_topc @ X8)
% 2.13/2.34          | ~ (m1_subset_1 @ (u1_struct_0 @ X7) @ 
% 2.13/2.34               (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 2.13/2.34          | (v4_pre_topc @ (u1_struct_0 @ X7) @ X8)
% 2.13/2.34          | ~ (v1_borsuk_1 @ X7 @ X8)
% 2.13/2.34          | ~ (m1_pre_topc @ X7 @ X8))),
% 2.13/2.34      inference('simplify', [status(thm)], ['21'])).
% 2.13/2.34  thf('23', plain,
% 2.13/2.34      (((v1_xboole_0 @ sk_B_1)
% 2.13/2.34        | ~ (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 2.13/2.34        | ~ (v1_borsuk_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 2.13/2.34        | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)) @ sk_A)
% 2.13/2.34        | ~ (l1_pre_topc @ sk_A)
% 2.13/2.34        | ~ (v2_pre_topc @ sk_A))),
% 2.13/2.34      inference('sup-', [status(thm)], ['20', '22'])).
% 2.13/2.34  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('26', plain,
% 2.13/2.34      (((v1_xboole_0 @ sk_B_1)
% 2.13/2.34        | ~ (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 2.13/2.34        | ~ (v1_borsuk_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 2.13/2.34        | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)) @ sk_A))),
% 2.13/2.34      inference('demod', [status(thm)], ['23', '24', '25'])).
% 2.13/2.34  thf('27', plain,
% 2.13/2.34      (((v1_xboole_0 @ sk_B_1)
% 2.13/2.34        | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)) @ sk_A)
% 2.13/2.34        | ~ (v1_borsuk_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 2.13/2.34        | (v1_xboole_0 @ sk_B_1))),
% 2.13/2.34      inference('sup-', [status(thm)], ['15', '26'])).
% 2.13/2.34  thf('28', plain,
% 2.13/2.34      ((~ (v1_borsuk_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 2.13/2.34        | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)) @ sk_A)
% 2.13/2.34        | (v1_xboole_0 @ sk_B_1))),
% 2.13/2.34      inference('simplify', [status(thm)], ['27'])).
% 2.13/2.34  thf('29', plain,
% 2.13/2.34      (((v1_xboole_0 @ sk_B_1) | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 2.13/2.34      inference('clc', [status(thm)], ['13', '14'])).
% 2.13/2.34  thf(cc5_tdlat_3, axiom,
% 2.13/2.34    (![A:$i]:
% 2.13/2.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 2.13/2.34         ( l1_pre_topc @ A ) ) =>
% 2.13/2.34       ( ![B:$i]:
% 2.13/2.34         ( ( m1_pre_topc @ B @ A ) =>
% 2.13/2.34           ( ( v1_borsuk_1 @ B @ A ) & ( v1_tsep_1 @ B @ A ) & 
% 2.13/2.34             ( v1_tdlat_3 @ B ) ) ) ) ))).
% 2.13/2.34  thf('30', plain,
% 2.13/2.34      (![X13 : $i, X14 : $i]:
% 2.13/2.34         (~ (m1_pre_topc @ X13 @ X14)
% 2.13/2.34          | (v1_borsuk_1 @ X13 @ X14)
% 2.13/2.34          | ~ (l1_pre_topc @ X14)
% 2.13/2.34          | ~ (v1_tdlat_3 @ X14)
% 2.13/2.34          | ~ (v2_pre_topc @ X14)
% 2.13/2.34          | (v2_struct_0 @ X14))),
% 2.13/2.34      inference('cnf', [status(esa)], [cc5_tdlat_3])).
% 2.13/2.34  thf('31', plain,
% 2.13/2.34      (((v1_xboole_0 @ sk_B_1)
% 2.13/2.34        | (v2_struct_0 @ sk_A)
% 2.13/2.34        | ~ (v2_pre_topc @ sk_A)
% 2.13/2.34        | ~ (v1_tdlat_3 @ sk_A)
% 2.13/2.34        | ~ (l1_pre_topc @ sk_A)
% 2.13/2.34        | (v1_borsuk_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 2.13/2.34      inference('sup-', [status(thm)], ['29', '30'])).
% 2.13/2.34  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('33', plain, ((v1_tdlat_3 @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('35', plain,
% 2.13/2.35      (((v1_xboole_0 @ sk_B_1)
% 2.13/2.35        | (v2_struct_0 @ sk_A)
% 2.13/2.35        | (v1_borsuk_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 2.13/2.35      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 2.13/2.35  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('37', plain,
% 2.13/2.35      (((v1_borsuk_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 2.13/2.35      inference('clc', [status(thm)], ['35', '36'])).
% 2.13/2.35  thf('38', plain,
% 2.13/2.35      (((v1_xboole_0 @ sk_B_1)
% 2.13/2.35        | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)) @ sk_A))),
% 2.13/2.35      inference('clc', [status(thm)], ['28', '37'])).
% 2.13/2.35  thf('39', plain,
% 2.13/2.35      (((v4_pre_topc @ sk_B_1 @ sk_A)
% 2.13/2.35        | (v1_xboole_0 @ sk_B_1)
% 2.13/2.35        | (v1_xboole_0 @ sk_B_1))),
% 2.13/2.35      inference('sup+', [status(thm)], ['8', '38'])).
% 2.13/2.35  thf('40', plain, (((v1_xboole_0 @ sk_B_1) | (v4_pre_topc @ sk_B_1 @ sk_A))),
% 2.13/2.35      inference('simplify', [status(thm)], ['39'])).
% 2.13/2.35  thf('41', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf(t52_pre_topc, axiom,
% 2.13/2.35    (![A:$i]:
% 2.13/2.35     ( ( l1_pre_topc @ A ) =>
% 2.13/2.35       ( ![B:$i]:
% 2.13/2.35         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.13/2.35           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 2.13/2.35             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 2.13/2.35               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 2.13/2.35  thf('42', plain,
% 2.13/2.35      (![X4 : $i, X5 : $i]:
% 2.13/2.35         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 2.13/2.35          | ~ (v4_pre_topc @ X4 @ X5)
% 2.13/2.35          | ((k2_pre_topc @ X5 @ X4) = (X4))
% 2.13/2.35          | ~ (l1_pre_topc @ X5))),
% 2.13/2.35      inference('cnf', [status(esa)], [t52_pre_topc])).
% 2.13/2.35  thf('43', plain,
% 2.13/2.35      ((~ (l1_pre_topc @ sk_A)
% 2.13/2.35        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 2.13/2.35        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 2.13/2.35      inference('sup-', [status(thm)], ['41', '42'])).
% 2.13/2.35  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('45', plain,
% 2.13/2.35      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 2.13/2.35        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 2.13/2.35      inference('demod', [status(thm)], ['43', '44'])).
% 2.13/2.35  thf('46', plain,
% 2.13/2.35      (((v1_xboole_0 @ sk_B_1) | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))),
% 2.13/2.35      inference('sup-', [status(thm)], ['40', '45'])).
% 2.13/2.35  thf('47', plain,
% 2.13/2.35      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 2.13/2.35        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('48', plain,
% 2.13/2.35      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 2.13/2.35      inference('split', [status(esa)], ['47'])).
% 2.13/2.35  thf('49', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf(t47_tex_2, axiom,
% 2.13/2.35    (![A:$i]:
% 2.13/2.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.13/2.35       ( ![B:$i]:
% 2.13/2.35         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.13/2.35           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 2.13/2.35             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 2.13/2.35  thf('50', plain,
% 2.13/2.35      (![X27 : $i, X28 : $i]:
% 2.13/2.35         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 2.13/2.35          | (v1_tops_1 @ X27 @ X28)
% 2.13/2.35          | ~ (v3_tex_2 @ X27 @ X28)
% 2.13/2.35          | ~ (v3_pre_topc @ X27 @ X28)
% 2.13/2.35          | ~ (l1_pre_topc @ X28)
% 2.13/2.35          | ~ (v2_pre_topc @ X28)
% 2.13/2.35          | (v2_struct_0 @ X28))),
% 2.13/2.35      inference('cnf', [status(esa)], [t47_tex_2])).
% 2.13/2.35  thf('51', plain,
% 2.13/2.35      (((v2_struct_0 @ sk_A)
% 2.13/2.35        | ~ (v2_pre_topc @ sk_A)
% 2.13/2.35        | ~ (l1_pre_topc @ sk_A)
% 2.13/2.35        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 2.13/2.35        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 2.13/2.35        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 2.13/2.35      inference('sup-', [status(thm)], ['49', '50'])).
% 2.13/2.35  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('54', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf(t17_tdlat_3, axiom,
% 2.13/2.35    (![A:$i]:
% 2.13/2.35     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.13/2.35       ( ( v1_tdlat_3 @ A ) <=>
% 2.13/2.35         ( ![B:$i]:
% 2.13/2.35           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.13/2.35             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 2.13/2.35  thf('55', plain,
% 2.13/2.35      (![X21 : $i, X22 : $i]:
% 2.13/2.35         (~ (v1_tdlat_3 @ X21)
% 2.13/2.35          | (v3_pre_topc @ X22 @ X21)
% 2.13/2.35          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 2.13/2.35          | ~ (l1_pre_topc @ X21)
% 2.13/2.35          | ~ (v2_pre_topc @ X21))),
% 2.13/2.35      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 2.13/2.35  thf('56', plain,
% 2.13/2.35      ((~ (v2_pre_topc @ sk_A)
% 2.13/2.35        | ~ (l1_pre_topc @ sk_A)
% 2.13/2.35        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 2.13/2.35        | ~ (v1_tdlat_3 @ sk_A))),
% 2.13/2.35      inference('sup-', [status(thm)], ['54', '55'])).
% 2.13/2.35  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('59', plain, ((v1_tdlat_3 @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('60', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 2.13/2.35      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 2.13/2.35  thf('61', plain,
% 2.13/2.35      (((v2_struct_0 @ sk_A)
% 2.13/2.35        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 2.13/2.35        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 2.13/2.35      inference('demod', [status(thm)], ['51', '52', '53', '60'])).
% 2.13/2.35  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('63', plain,
% 2.13/2.35      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 2.13/2.35      inference('clc', [status(thm)], ['61', '62'])).
% 2.13/2.35  thf('64', plain,
% 2.13/2.35      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 2.13/2.35      inference('sup-', [status(thm)], ['48', '63'])).
% 2.13/2.35  thf('65', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf(d2_tops_3, axiom,
% 2.13/2.35    (![A:$i]:
% 2.13/2.35     ( ( l1_pre_topc @ A ) =>
% 2.13/2.35       ( ![B:$i]:
% 2.13/2.35         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.13/2.35           ( ( v1_tops_1 @ B @ A ) <=>
% 2.13/2.35             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 2.13/2.35  thf('66', plain,
% 2.13/2.35      (![X15 : $i, X16 : $i]:
% 2.13/2.35         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 2.13/2.35          | ~ (v1_tops_1 @ X15 @ X16)
% 2.13/2.35          | ((k2_pre_topc @ X16 @ X15) = (u1_struct_0 @ X16))
% 2.13/2.35          | ~ (l1_pre_topc @ X16))),
% 2.13/2.35      inference('cnf', [status(esa)], [d2_tops_3])).
% 2.13/2.35  thf('67', plain,
% 2.13/2.35      ((~ (l1_pre_topc @ sk_A)
% 2.13/2.35        | ((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 2.13/2.35        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 2.13/2.35      inference('sup-', [status(thm)], ['65', '66'])).
% 2.13/2.35  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('69', plain,
% 2.13/2.35      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 2.13/2.35        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 2.13/2.35      inference('demod', [status(thm)], ['67', '68'])).
% 2.13/2.35  thf('70', plain,
% 2.13/2.35      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 2.13/2.35         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 2.13/2.35      inference('sup-', [status(thm)], ['64', '69'])).
% 2.13/2.35  thf('71', plain,
% 2.13/2.35      (((((sk_B_1) = (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1)))
% 2.13/2.35         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 2.13/2.35      inference('sup+', [status(thm)], ['46', '70'])).
% 2.13/2.35  thf('72', plain,
% 2.13/2.35      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 2.13/2.35      inference('split', [status(esa)], ['47'])).
% 2.13/2.35  thf('73', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf(t46_tex_2, axiom,
% 2.13/2.35    (![A:$i]:
% 2.13/2.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.13/2.35       ( ![B:$i]:
% 2.13/2.35         ( ( ( v1_xboole_0 @ B ) & 
% 2.13/2.35             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.13/2.35           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 2.13/2.35  thf('74', plain,
% 2.13/2.35      (![X25 : $i, X26 : $i]:
% 2.13/2.35         (~ (v1_xboole_0 @ X25)
% 2.13/2.35          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 2.13/2.35          | ~ (v3_tex_2 @ X25 @ X26)
% 2.13/2.35          | ~ (l1_pre_topc @ X26)
% 2.13/2.35          | ~ (v2_pre_topc @ X26)
% 2.13/2.35          | (v2_struct_0 @ X26))),
% 2.13/2.35      inference('cnf', [status(esa)], [t46_tex_2])).
% 2.13/2.35  thf('75', plain,
% 2.13/2.35      (((v2_struct_0 @ sk_A)
% 2.13/2.35        | ~ (v2_pre_topc @ sk_A)
% 2.13/2.35        | ~ (l1_pre_topc @ sk_A)
% 2.13/2.35        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 2.13/2.35        | ~ (v1_xboole_0 @ sk_B_1))),
% 2.13/2.35      inference('sup-', [status(thm)], ['73', '74'])).
% 2.13/2.35  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('78', plain,
% 2.13/2.35      (((v2_struct_0 @ sk_A)
% 2.13/2.35        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 2.13/2.35        | ~ (v1_xboole_0 @ sk_B_1))),
% 2.13/2.35      inference('demod', [status(thm)], ['75', '76', '77'])).
% 2.13/2.35  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('80', plain, ((~ (v1_xboole_0 @ sk_B_1) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 2.13/2.35      inference('clc', [status(thm)], ['78', '79'])).
% 2.13/2.35  thf('81', plain,
% 2.13/2.35      ((~ (v1_xboole_0 @ sk_B_1)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 2.13/2.35      inference('sup-', [status(thm)], ['72', '80'])).
% 2.13/2.35  thf('82', plain,
% 2.13/2.35      ((((sk_B_1) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 2.13/2.35      inference('clc', [status(thm)], ['71', '81'])).
% 2.13/2.35  thf('83', plain,
% 2.13/2.35      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 2.13/2.35         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 2.13/2.35      inference('split', [status(esa)], ['0'])).
% 2.13/2.35  thf('84', plain,
% 2.13/2.35      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 2.13/2.35         <= (((v3_tex_2 @ sk_B_1 @ sk_A)) & 
% 2.13/2.35             ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 2.13/2.35      inference('sup+', [status(thm)], ['82', '83'])).
% 2.13/2.35  thf(fc14_subset_1, axiom,
% 2.13/2.35    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 2.13/2.35  thf('85', plain, (![X1 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X1) @ X1)),
% 2.13/2.35      inference('cnf', [status(esa)], [fc14_subset_1])).
% 2.13/2.35  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 2.13/2.35  thf('86', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 2.13/2.35      inference('cnf', [status(esa)], [d4_subset_1])).
% 2.13/2.35  thf('87', plain, (![X1 : $i]: ~ (v1_subset_1 @ X1 @ X1)),
% 2.13/2.35      inference('demod', [status(thm)], ['85', '86'])).
% 2.13/2.35  thf('88', plain,
% 2.13/2.35      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 2.13/2.35       ~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 2.13/2.35      inference('sup-', [status(thm)], ['84', '87'])).
% 2.13/2.35  thf('89', plain,
% 2.13/2.35      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 2.13/2.35       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 2.13/2.35      inference('split', [status(esa)], ['47'])).
% 2.13/2.35  thf(d3_struct_0, axiom,
% 2.13/2.35    (![A:$i]:
% 2.13/2.35     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 2.13/2.35  thf('90', plain,
% 2.13/2.35      (![X2 : $i]:
% 2.13/2.35         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 2.13/2.35      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.13/2.35  thf('91', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf(d7_subset_1, axiom,
% 2.13/2.35    (![A:$i,B:$i]:
% 2.13/2.35     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.13/2.35       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 2.13/2.35  thf('92', plain,
% 2.13/2.35      (![X17 : $i, X18 : $i]:
% 2.13/2.35         (((X18) = (X17))
% 2.13/2.35          | (v1_subset_1 @ X18 @ X17)
% 2.13/2.35          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 2.13/2.35      inference('cnf', [status(esa)], [d7_subset_1])).
% 2.13/2.35  thf('93', plain,
% 2.13/2.35      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 2.13/2.35        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 2.13/2.35      inference('sup-', [status(thm)], ['91', '92'])).
% 2.13/2.35  thf('94', plain,
% 2.13/2.35      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 2.13/2.35         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 2.13/2.35      inference('split', [status(esa)], ['47'])).
% 2.13/2.35  thf('95', plain,
% 2.13/2.35      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 2.13/2.35         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 2.13/2.35      inference('sup-', [status(thm)], ['93', '94'])).
% 2.13/2.35  thf('96', plain,
% 2.13/2.35      (((((sk_B_1) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 2.13/2.35         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 2.13/2.35      inference('sup+', [status(thm)], ['90', '95'])).
% 2.13/2.35  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf(dt_l1_pre_topc, axiom,
% 2.13/2.35    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 2.13/2.35  thf('98', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 2.13/2.35      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 2.13/2.35  thf('99', plain, ((l1_struct_0 @ sk_A)),
% 2.13/2.35      inference('sup-', [status(thm)], ['97', '98'])).
% 2.13/2.35  thf('100', plain,
% 2.13/2.35      ((((sk_B_1) = (k2_struct_0 @ sk_A)))
% 2.13/2.35         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 2.13/2.35      inference('demod', [status(thm)], ['96', '99'])).
% 2.13/2.35  thf(t27_tops_1, axiom,
% 2.13/2.35    (![A:$i]:
% 2.13/2.35     ( ( l1_pre_topc @ A ) =>
% 2.13/2.35       ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 2.13/2.35  thf('101', plain,
% 2.13/2.35      (![X6 : $i]:
% 2.13/2.35         (((k2_pre_topc @ X6 @ (k2_struct_0 @ X6)) = (k2_struct_0 @ X6))
% 2.13/2.35          | ~ (l1_pre_topc @ X6))),
% 2.13/2.35      inference('cnf', [status(esa)], [t27_tops_1])).
% 2.13/2.35  thf('102', plain,
% 2.13/2.35      (((((k2_pre_topc @ sk_A @ sk_B_1) = (k2_struct_0 @ sk_A))
% 2.13/2.35         | ~ (l1_pre_topc @ sk_A)))
% 2.13/2.35         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 2.13/2.35      inference('sup+', [status(thm)], ['100', '101'])).
% 2.13/2.35  thf('103', plain,
% 2.13/2.35      ((((sk_B_1) = (k2_struct_0 @ sk_A)))
% 2.13/2.35         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 2.13/2.35      inference('demod', [status(thm)], ['96', '99'])).
% 2.13/2.35  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('105', plain,
% 2.13/2.35      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 2.13/2.35         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 2.13/2.35      inference('demod', [status(thm)], ['102', '103', '104'])).
% 2.13/2.35  thf('106', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('107', plain,
% 2.13/2.35      (![X15 : $i, X16 : $i]:
% 2.13/2.35         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 2.13/2.35          | ((k2_pre_topc @ X16 @ X15) != (u1_struct_0 @ X16))
% 2.13/2.35          | (v1_tops_1 @ X15 @ X16)
% 2.13/2.35          | ~ (l1_pre_topc @ X16))),
% 2.13/2.35      inference('cnf', [status(esa)], [d2_tops_3])).
% 2.13/2.35  thf('108', plain,
% 2.13/2.35      ((~ (l1_pre_topc @ sk_A)
% 2.13/2.35        | (v1_tops_1 @ sk_B_1 @ sk_A)
% 2.13/2.35        | ((k2_pre_topc @ sk_A @ sk_B_1) != (u1_struct_0 @ sk_A)))),
% 2.13/2.35      inference('sup-', [status(thm)], ['106', '107'])).
% 2.13/2.35  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('110', plain,
% 2.13/2.35      (((v1_tops_1 @ sk_B_1 @ sk_A)
% 2.13/2.35        | ((k2_pre_topc @ sk_A @ sk_B_1) != (u1_struct_0 @ sk_A)))),
% 2.13/2.35      inference('demod', [status(thm)], ['108', '109'])).
% 2.13/2.35  thf('111', plain,
% 2.13/2.35      (((((sk_B_1) != (u1_struct_0 @ sk_A)) | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 2.13/2.35         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 2.13/2.35      inference('sup-', [status(thm)], ['105', '110'])).
% 2.13/2.35  thf('112', plain,
% 2.13/2.35      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 2.13/2.35         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 2.13/2.35      inference('sup-', [status(thm)], ['93', '94'])).
% 2.13/2.35  thf('113', plain,
% 2.13/2.35      (((((sk_B_1) != (sk_B_1)) | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 2.13/2.35         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 2.13/2.35      inference('demod', [status(thm)], ['111', '112'])).
% 2.13/2.35  thf('114', plain,
% 2.13/2.35      (((v1_tops_1 @ sk_B_1 @ sk_A))
% 2.13/2.35         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 2.13/2.35      inference('simplify', [status(thm)], ['113'])).
% 2.13/2.35  thf('115', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf(t48_tex_2, axiom,
% 2.13/2.35    (![A:$i]:
% 2.13/2.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.13/2.35       ( ![B:$i]:
% 2.13/2.35         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.13/2.35           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 2.13/2.35             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 2.13/2.35  thf('116', plain,
% 2.13/2.35      (![X29 : $i, X30 : $i]:
% 2.13/2.35         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 2.13/2.35          | (v3_tex_2 @ X29 @ X30)
% 2.13/2.35          | ~ (v2_tex_2 @ X29 @ X30)
% 2.13/2.35          | ~ (v1_tops_1 @ X29 @ X30)
% 2.13/2.35          | ~ (l1_pre_topc @ X30)
% 2.13/2.35          | ~ (v2_pre_topc @ X30)
% 2.13/2.35          | (v2_struct_0 @ X30))),
% 2.13/2.35      inference('cnf', [status(esa)], [t48_tex_2])).
% 2.13/2.35  thf('117', plain,
% 2.13/2.35      (((v2_struct_0 @ sk_A)
% 2.13/2.35        | ~ (v2_pre_topc @ sk_A)
% 2.13/2.35        | ~ (l1_pre_topc @ sk_A)
% 2.13/2.35        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 2.13/2.35        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 2.13/2.35        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 2.13/2.35      inference('sup-', [status(thm)], ['115', '116'])).
% 2.13/2.35  thf('118', plain, ((v2_pre_topc @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('120', plain,
% 2.13/2.35      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf(t43_tex_2, axiom,
% 2.13/2.35    (![A:$i]:
% 2.13/2.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 2.13/2.35         ( l1_pre_topc @ A ) ) =>
% 2.13/2.35       ( ![B:$i]:
% 2.13/2.35         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.13/2.35           ( v2_tex_2 @ B @ A ) ) ) ))).
% 2.13/2.35  thf('121', plain,
% 2.13/2.35      (![X23 : $i, X24 : $i]:
% 2.13/2.35         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 2.13/2.35          | (v2_tex_2 @ X23 @ X24)
% 2.13/2.35          | ~ (l1_pre_topc @ X24)
% 2.13/2.35          | ~ (v1_tdlat_3 @ X24)
% 2.13/2.35          | ~ (v2_pre_topc @ X24)
% 2.13/2.35          | (v2_struct_0 @ X24))),
% 2.13/2.35      inference('cnf', [status(esa)], [t43_tex_2])).
% 2.13/2.35  thf('122', plain,
% 2.13/2.35      (((v2_struct_0 @ sk_A)
% 2.13/2.35        | ~ (v2_pre_topc @ sk_A)
% 2.13/2.35        | ~ (v1_tdlat_3 @ sk_A)
% 2.13/2.35        | ~ (l1_pre_topc @ sk_A)
% 2.13/2.35        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 2.13/2.35      inference('sup-', [status(thm)], ['120', '121'])).
% 2.13/2.35  thf('123', plain, ((v2_pre_topc @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('124', plain, ((v1_tdlat_3 @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('126', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 2.13/2.35      inference('demod', [status(thm)], ['122', '123', '124', '125'])).
% 2.13/2.35  thf('127', plain, (~ (v2_struct_0 @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('128', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 2.13/2.35      inference('clc', [status(thm)], ['126', '127'])).
% 2.13/2.35  thf('129', plain,
% 2.13/2.35      (((v2_struct_0 @ sk_A)
% 2.13/2.35        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 2.13/2.35        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 2.13/2.35      inference('demod', [status(thm)], ['117', '118', '119', '128'])).
% 2.13/2.35  thf('130', plain, (~ (v2_struct_0 @ sk_A)),
% 2.13/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.35  thf('131', plain,
% 2.13/2.35      (((v3_tex_2 @ sk_B_1 @ sk_A) | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 2.13/2.35      inference('clc', [status(thm)], ['129', '130'])).
% 2.13/2.35  thf('132', plain,
% 2.13/2.35      (((v3_tex_2 @ sk_B_1 @ sk_A))
% 2.13/2.35         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 2.13/2.35      inference('sup-', [status(thm)], ['114', '131'])).
% 2.13/2.35  thf('133', plain,
% 2.13/2.35      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 2.13/2.35      inference('split', [status(esa)], ['0'])).
% 2.13/2.35  thf('134', plain,
% 2.13/2.35      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 2.13/2.35       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 2.13/2.35      inference('sup-', [status(thm)], ['132', '133'])).
% 2.13/2.35  thf('135', plain, ($false),
% 2.13/2.35      inference('sat_resolution*', [status(thm)], ['1', '88', '89', '134'])).
% 2.13/2.35  
% 2.13/2.35  % SZS output end Refutation
% 2.13/2.35  
% 2.13/2.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
