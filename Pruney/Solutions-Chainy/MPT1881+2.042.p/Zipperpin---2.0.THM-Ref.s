%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bK2s8imIxT

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 366 expanded)
%              Number of leaves         :   30 ( 115 expanded)
%              Depth                    :   16
%              Number of atoms          :  853 (4426 expanded)
%              Number of equality atoms :   26 (  52 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

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
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_tops_1 @ X16 @ X17 )
      | ~ ( v3_tex_2 @ X16 @ X17 )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_tdlat_3 @ X12 )
      | ( v3_pre_topc @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('12',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v1_tops_1 @ X8 @ X9 )
      | ( ( k2_pre_topc @ X9 @ X8 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v4_pre_topc @ X4 @ X5 )
      | ( ( k2_pre_topc @ X5 @ X4 )
        = X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X7 ) @ X6 ) @ X7 )
      | ( v4_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('37',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_tdlat_3 @ X12 )
      | ( v3_pre_topc @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('39',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['33','34','43'])).

thf('45',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['30','44'])).

thf('46',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','45'])).

thf('47',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','46'])).

thf('48',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('50',plain,(
    ! [X3: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X3 ) @ X3 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('52',plain,(
    ! [X3: $i] :
      ~ ( v1_subset_1 @ X3 @ X3 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','53','54'])).

thf('56',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','55'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_tex_2 @ X18 @ X19 )
      | ~ ( v2_tex_2 @ X18 @ X19 )
      | ~ ( v1_tops_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v2_tex_2 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_tdlat_3 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61','70'])).

thf('72',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['30','44'])).

thf('73',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('74',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11 = X10 )
      | ( v1_subset_1 @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('75',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('77',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('81',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k2_pre_topc @ X9 @ X8 )
       != ( u1_struct_0 @ X9 ) )
      | ( v1_tops_1 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
       != sk_B_1 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','85'])).

thf('87',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','86'])).

thf('88',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','53'])).

thf('90',plain,(
    v1_tops_1 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['71','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['56','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bK2s8imIxT
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:06:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 158 iterations in 0.076s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.52  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.52  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.21/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.52  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(t49_tex_2, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.21/0.52         ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.52             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.52            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52              ( ( v3_tex_2 @ B @ A ) <=>
% 0.21/0.52                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.21/0.52       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.52      inference('split', [status(esa)], ['2'])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.52      inference('split', [status(esa)], ['2'])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t47_tex_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.21/0.52             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.52          | (v1_tops_1 @ X16 @ X17)
% 0.21/0.52          | ~ (v3_tex_2 @ X16 @ X17)
% 0.21/0.52          | ~ (v3_pre_topc @ X16 @ X17)
% 0.21/0.52          | ~ (l1_pre_topc @ X17)
% 0.21/0.52          | ~ (v2_pre_topc @ X17)
% 0.21/0.52          | (v2_struct_0 @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.21/0.52        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.52        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t17_tdlat_3, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ( v1_tdlat_3 @ A ) <=>
% 0.21/0.52         ( ![B:$i]:
% 0.21/0.52           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (v1_tdlat_3 @ X12)
% 0.21/0.52          | (v3_pre_topc @ X13 @ X12)
% 0.21/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.52          | ~ (l1_pre_topc @ X12)
% 0.21/0.52          | ~ (v2_pre_topc @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.21/0.52        | ~ (v1_tdlat_3 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('15', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('16', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.52        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['7', '8', '9', '16'])).
% 0.21/0.52  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['4', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d2_tops_3, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( v1_tops_1 @ B @ A ) <=>
% 0.21/0.52             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.52          | ~ (v1_tops_1 @ X8 @ X9)
% 0.21/0.52          | ((k2_pre_topc @ X9 @ X8) = (u1_struct_0 @ X9))
% 0.21/0.52          | ~ (l1_pre_topc @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | ((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.21/0.52        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.21/0.52        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t52_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.21/0.52             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.21/0.52               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.21/0.52          | ~ (v4_pre_topc @ X4 @ X5)
% 0.21/0.52          | ((k2_pre_topc @ X5 @ X4) = (X4))
% 0.21/0.52          | ~ (l1_pre_topc @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.21/0.52        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.21/0.52        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t29_tops_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( v4_pre_topc @ B @ A ) <=>
% 0.21/0.52             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.52          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X7) @ X6) @ X7)
% 0.21/0.52          | (v4_pre_topc @ X6 @ X7)
% 0.21/0.52          | ~ (l1_pre_topc @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.21/0.52        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.52  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k3_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i]:
% 0.21/0.52         ((m1_subset_1 @ (k3_subset_1 @ X1 @ X2) @ (k1_zfmisc_1 @ X1))
% 0.21/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (v1_tdlat_3 @ X12)
% 0.21/0.52          | (v3_pre_topc @ X13 @ X12)
% 0.21/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.52          | ~ (l1_pre_topc @ X12)
% 0.21/0.52          | ~ (v2_pre_topc @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.21/0.52        | ~ (v1_tdlat_3 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.52  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('42', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.21/0.52  thf('44', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['33', '34', '43'])).
% 0.21/0.52  thf('45', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['30', '44'])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      ((((sk_B_1) = (u1_struct_0 @ sk_A)) | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '45'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      ((((sk_B_1) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['20', '46'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.21/0.52         <= (((v3_tex_2 @ sk_B_1 @ sk_A)) & 
% 0.21/0.52             ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['47', '48'])).
% 0.21/0.52  thf(fc14_subset_1, axiom,
% 0.21/0.52    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.21/0.52  thf('50', plain, (![X3 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X3) @ X3)),
% 0.21/0.52      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.21/0.52  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.52  thf('51', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.52  thf('52', plain, (![X3 : $i]: ~ (v1_subset_1 @ X3 @ X3)),
% 0.21/0.52      inference('demod', [status(thm)], ['50', '51'])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.21/0.52       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['49', '52'])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.21/0.52       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('55', plain, (~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['3', '53', '54'])).
% 0.21/0.52  thf('56', plain, (~ (v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['1', '55'])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t48_tex_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.21/0.52             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.52          | (v3_tex_2 @ X18 @ X19)
% 0.21/0.52          | ~ (v2_tex_2 @ X18 @ X19)
% 0.21/0.52          | ~ (v1_tops_1 @ X18 @ X19)
% 0.21/0.52          | ~ (l1_pre_topc @ X19)
% 0.21/0.52          | ~ (v2_pre_topc @ X19)
% 0.21/0.52          | (v2_struct_0 @ X19))),
% 0.21/0.52      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.21/0.52        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.21/0.52        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.52  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('62', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t43_tex_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.21/0.52         ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.52          | (v2_tex_2 @ X14 @ X15)
% 0.21/0.52          | ~ (l1_pre_topc @ X15)
% 0.21/0.52          | ~ (v1_tdlat_3 @ X15)
% 0.21/0.52          | ~ (v2_pre_topc @ X15)
% 0.21/0.52          | (v2_struct_0 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (v1_tdlat_3 @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.52  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('66', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('68', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.21/0.52  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('70', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.21/0.52      inference('clc', [status(thm)], ['68', '69'])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.21/0.52        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['59', '60', '61', '70'])).
% 0.21/0.52  thf('72', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['30', '44'])).
% 0.21/0.52  thf('73', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d7_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.21/0.52  thf('74', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i]:
% 0.21/0.52         (((X11) = (X10))
% 0.21/0.52          | (v1_subset_1 @ X11 @ X10)
% 0.21/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.52  thf('75', plain,
% 0.21/0.52      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.52  thf('76', plain,
% 0.21/0.52      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('split', [status(esa)], ['2'])).
% 0.21/0.52  thf('77', plain,
% 0.21/0.52      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.21/0.52         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.52  thf('78', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('79', plain,
% 0.21/0.52      (((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_B_1)))
% 0.21/0.52         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['77', '78'])).
% 0.21/0.52  thf('80', plain,
% 0.21/0.52      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.21/0.52         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.52  thf('81', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.52          | ((k2_pre_topc @ X9 @ X8) != (u1_struct_0 @ X9))
% 0.21/0.52          | (v1_tops_1 @ X8 @ X9)
% 0.21/0.52          | ~ (l1_pre_topc @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.21/0.52  thf('82', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.21/0.52           | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52           | (v1_tops_1 @ X0 @ sk_A)
% 0.21/0.52           | ((k2_pre_topc @ sk_A @ X0) != (u1_struct_0 @ sk_A))))
% 0.21/0.52         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['80', '81'])).
% 0.21/0.52  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('84', plain,
% 0.21/0.52      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.21/0.52         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.52  thf('85', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.21/0.52           | (v1_tops_1 @ X0 @ sk_A)
% 0.21/0.52           | ((k2_pre_topc @ sk_A @ X0) != (sk_B_1))))
% 0.21/0.52         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.21/0.52  thf('86', plain,
% 0.21/0.52      (((((k2_pre_topc @ sk_A @ sk_B_1) != (sk_B_1))
% 0.21/0.52         | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.21/0.52         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['79', '85'])).
% 0.21/0.52  thf('87', plain,
% 0.21/0.52      (((((sk_B_1) != (sk_B_1)) | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.21/0.52         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['72', '86'])).
% 0.21/0.52  thf('88', plain,
% 0.21/0.52      (((v1_tops_1 @ sk_B_1 @ sk_A))
% 0.21/0.52         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['87'])).
% 0.21/0.52  thf('89', plain, (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['3', '53'])).
% 0.21/0.52  thf('90', plain, ((v1_tops_1 @ sk_B_1 @ sk_A)),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['88', '89'])).
% 0.21/0.52  thf('91', plain, (((v2_struct_0 @ sk_A) | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['71', '90'])).
% 0.21/0.52  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('93', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.21/0.52      inference('clc', [status(thm)], ['91', '92'])).
% 0.21/0.52  thf('94', plain, ($false), inference('demod', [status(thm)], ['56', '93'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
