%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HlC3D3rfyH

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 364 expanded)
%              Number of leaves         :   33 ( 120 expanded)
%              Depth                    :   15
%              Number of atoms          :  694 (4322 expanded)
%              Number of equality atoms :   29 (  92 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(t61_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ~ ( ( ( v3_pre_topc @ B @ A )
                | ( v4_pre_topc @ B @ A ) )
              & ( v3_tex_2 @ B @ A )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ~ ( ( ( v3_pre_topc @ B @ A )
                  | ( v4_pre_topc @ B @ A ) )
                & ( v3_tex_2 @ B @ A )
                & ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_tex_2])).

thf('0',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( v4_pre_topc @ X2 @ X3 )
      | ( ( k2_pre_topc @ X3 @ X2 )
        = X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_tops_1 @ X15 @ X16 )
      | ~ ( v3_tex_2 @ X15 @ X16 )
      | ~ ( v3_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v1_tops_1 @ X9 @ X10 )
      | ( ( k2_pre_topc @ X10 @ X9 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('27',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_tdlat_3 @ X11 )
      | ~ ( v3_pre_topc @ X12 @ X11 )
      | ( v4_pre_topc @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t23_tdlat_3])).

thf('29',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('36',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','36'])).

thf('38',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_subset_1 @ sk_B_2 @ sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('40',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('41',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('43',plain,(
    ! [X7: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X6: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('49',plain,(
    ! [X1: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ X0 @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','54'])).

thf('56',plain,(
    ! [X6: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('57',plain,(
    ! [X0: $i] :
      ~ ( v1_subset_1 @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','57'])).

thf('59',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('60',plain,(
    v4_pre_topc @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_2 )
    = sk_B_2 ),
    inference(simpl_trail,[status(thm)],['8','60'])).

thf('62',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('63',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('64',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_tdlat_3 @ X13 )
      | ~ ( v4_pre_topc @ X14 @ X13 )
      | ( v3_pre_topc @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('65',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('72',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('74',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v4_pre_topc @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['58','59'])).

thf('76',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['74','75'])).

thf('77',plain,
    ( sk_B_2
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['61','76'])).

thf('78',plain,(
    v1_subset_1 @ sk_B_2 @ sk_B_2 ),
    inference(demod,[status(thm)],['0','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ~ ( v1_subset_1 @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('80',plain,(
    $false ),
    inference('sup-',[status(thm)],['78','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HlC3D3rfyH
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 116 iterations in 0.068s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.52  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.52  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.20/0.52  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.20/0.52  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.52  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.52  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.52  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.52  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.52  thf(t61_tex_2, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.52         ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.20/0.52                ( v3_tex_2 @ B @ A ) & 
% 0.20/0.52                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.20/0.52                   ( v3_tex_2 @ B @ A ) & 
% 0.20/0.52                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 0.20/0.52  thf('0', plain, ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (((v3_pre_topc @ sk_B_2 @ sk_A) | (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['1'])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t52_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.52             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.52               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.52          | ~ (v4_pre_topc @ X2 @ X3)
% 0.20/0.52          | ((k2_pre_topc @ X3 @ X2) = (X2))
% 0.20/0.52          | ~ (l1_pre_topc @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.20/0.52        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.20/0.52        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))
% 0.20/0.52         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '7'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['1'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t47_tex_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.20/0.52             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.52          | (v1_tops_1 @ X15 @ X16)
% 0.20/0.52          | ~ (v3_tex_2 @ X15 @ X16)
% 0.20/0.52          | ~ (v3_pre_topc @ X15 @ X16)
% 0.20/0.52          | ~ (l1_pre_topc @ X16)
% 0.20/0.52          | ~ (v2_pre_topc @ X16)
% 0.20/0.52          | (v2_struct_0 @ X16))),
% 0.20/0.52      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.20/0.52        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 0.20/0.52        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('15', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.20/0.52        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.20/0.52  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d2_tops_3, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( v1_tops_1 @ B @ A ) <=>
% 0.20/0.52             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.52          | ~ (v1_tops_1 @ X9 @ X10)
% 0.20/0.52          | ((k2_pre_topc @ X10 @ X9) = (u1_struct_0 @ X10))
% 0.20/0.52          | ~ (l1_pre_topc @ X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.20/0.52        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.20/0.52        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.20/0.52         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['19', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['1'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t23_tdlat_3, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ( v3_tdlat_3 @ A ) <=>
% 0.20/0.52         ( ![B:$i]:
% 0.20/0.52           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52             ( ( v3_pre_topc @ B @ A ) => ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X11 : $i, X12 : $i]:
% 0.20/0.52         (~ (v3_tdlat_3 @ X11)
% 0.20/0.52          | ~ (v3_pre_topc @ X12 @ X11)
% 0.20/0.52          | (v4_pre_topc @ X12 @ X11)
% 0.20/0.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.52          | ~ (l1_pre_topc @ X11)
% 0.20/0.52          | ~ (v2_pre_topc @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t23_tdlat_3])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (v4_pre_topc @ sk_B_2 @ sk_A)
% 0.20/0.52        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.20/0.52        | ~ (v3_tdlat_3 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('32', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (((v4_pre_topc @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '33'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.20/0.52        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))
% 0.20/0.52         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['25', '36'])).
% 0.20/0.52  thf('38', plain, ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (((v1_subset_1 @ sk_B_2 @ sk_B_2)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.52  thf(dt_l1_orders_2, axiom,
% 0.20/0.52    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.52  thf('40', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_orders_2 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.20/0.52  thf('41', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_orders_2 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.20/0.52  thf(d3_struct_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.52  thf(t1_yellow_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.20/0.52       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.52  thf('43', plain, (![X7 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X7)) = (X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))
% 0.20/0.52          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.20/0.52          | ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '44'])).
% 0.20/0.52  thf(dt_k2_yellow_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.52       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.20/0.52  thf('46', plain, (![X6 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.52  thf('47', plain, (![X0 : $i]: ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.52  thf(fc12_struct_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_struct_0 @ A ) =>
% 0.20/0.52       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X1 : $i]:
% 0.20/0.52         (~ (v1_subset_1 @ (k2_struct_0 @ X1) @ (u1_struct_0 @ X1))
% 0.20/0.52          | ~ (l1_struct_0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.20/0.52          | ~ (l1_struct_0 @ X0)
% 0.20/0.52          | ~ (l1_struct_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_struct_0 @ X0)
% 0.20/0.52          | ~ (v1_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_subset_1 @ (k2_struct_0 @ (k2_yellow_1 @ X0)) @ X0)
% 0.20/0.52          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['47', '51'])).
% 0.20/0.52  thf('53', plain, (![X0 : $i]: ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_subset_1 @ X0 @ X0) | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_orders_2 @ (k2_yellow_1 @ X0)) | ~ (v1_subset_1 @ X0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['40', '54'])).
% 0.20/0.52  thf('56', plain, (![X6 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.52  thf('57', plain, (![X0 : $i]: ~ (v1_subset_1 @ X0 @ X0)),
% 0.20/0.52      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.52  thf('58', plain, (~ ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['39', '57'])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      (((v4_pre_topc @ sk_B_2 @ sk_A)) | ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('split', [status(esa)], ['1'])).
% 0.20/0.52  thf('60', plain, (((v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['58', '59'])).
% 0.20/0.52  thf('61', plain, (((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['8', '60'])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['1'])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t24_tdlat_3, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ( v3_tdlat_3 @ A ) <=>
% 0.20/0.52         ( ![B:$i]:
% 0.20/0.52           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         (~ (v3_tdlat_3 @ X13)
% 0.20/0.52          | ~ (v4_pre_topc @ X14 @ X13)
% 0.20/0.52          | (v3_pre_topc @ X14 @ X13)
% 0.20/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.52          | ~ (l1_pre_topc @ X13)
% 0.20/0.52          | ~ (v2_pre_topc @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.20/0.52        | ~ (v4_pre_topc @ sk_B_2 @ sk_A)
% 0.20/0.52        | ~ (v3_tdlat_3 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.52  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('68', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      (((v3_pre_topc @ sk_B_2 @ sk_A) | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.20/0.52  thf('70', plain,
% 0.20/0.52      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['62', '69'])).
% 0.20/0.52  thf('71', plain,
% 0.20/0.52      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.52  thf('73', plain,
% 0.20/0.52      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.20/0.52        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('74', plain,
% 0.20/0.52      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.20/0.52         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.52  thf('75', plain, (((v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['58', '59'])).
% 0.20/0.52  thf('76', plain, (((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['74', '75'])).
% 0.20/0.52  thf('77', plain, (((sk_B_2) = (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup+', [status(thm)], ['61', '76'])).
% 0.20/0.52  thf('78', plain, ((v1_subset_1 @ sk_B_2 @ sk_B_2)),
% 0.20/0.52      inference('demod', [status(thm)], ['0', '77'])).
% 0.20/0.52  thf('79', plain, (![X0 : $i]: ~ (v1_subset_1 @ X0 @ X0)),
% 0.20/0.52      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.52  thf('80', plain, ($false), inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
