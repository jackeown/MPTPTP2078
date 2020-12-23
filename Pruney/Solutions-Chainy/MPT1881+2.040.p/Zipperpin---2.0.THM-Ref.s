%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PudRQ4o8Do

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 898 expanded)
%              Number of leaves         :   33 ( 268 expanded)
%              Depth                    :   18
%              Number of atoms          : 1148 (11265 expanded)
%              Number of equality atoms :   38 ( 141 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_tops_1 @ X19 @ X20 )
      | ~ ( v3_tex_2 @ X19 @ X20 )
      | ~ ( v3_pre_topc @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_tdlat_3 @ X15 )
      | ( v3_pre_topc @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v1_tops_1 @ X11 @ X12 )
      | ( ( k2_pre_topc @ X12 @ X11 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v4_pre_topc @ X7 @ X8 )
      | ( ( k2_pre_topc @ X8 @ X7 )
        = X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
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

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('33',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc3_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v3_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( v3_pre_topc @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X9 ) @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_tops_1])).

thf('35',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('38',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','38','39','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('43',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_tdlat_3 @ X15 )
      | ( v3_pre_topc @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('44',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['41','48'])).

thf('50',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['30','49'])).

thf('51',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','50'])).

thf('52',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','51'])).

thf('53',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','51'])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('56',plain,(
    ! [X6: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X6 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('57',plain,
    ( ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('59',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['57','60'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('62',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','51'])).

thf('64',plain,
    ( ( ( sk_B_1
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('66',plain,
    ( ( sk_B_1
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('68',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','67'])).

thf('69',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','68','69'])).

thf('71',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','70'])).

thf('72',plain,(
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

thf('73',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v3_tex_2 @ X21 @ X22 )
      | ~ ( v2_tex_2 @ X21 @ X22 )
      | ~ ( v1_tops_1 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
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

thf('78',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v2_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v1_tdlat_3 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75','76','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('88',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14 = X13 )
      | ( v1_subset_1 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('89',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('91',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('95',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k2_pre_topc @ X12 @ X11 )
       != ( u1_struct_0 @ X12 ) )
      | ( v1_tops_1 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
       != sk_B_1 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf('101',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('102',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','38','39','40'])).

thf('103',plain,
    ( ( ~ ( v3_pre_topc @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) @ sk_A )
      | ( v4_pre_topc @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('105',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('106',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('108',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('110',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_tdlat_3 @ X15 )
      | ( v3_pre_topc @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('111',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( v1_tdlat_3 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( v3_pre_topc @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('116',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','115'])).

thf('117',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','116'])).

thf('118',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('119',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','119'])).

thf('121',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','68'])).

thf('123',plain,(
    v1_tops_1 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['86','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    $false ),
    inference(demod,[status(thm)],['71','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PudRQ4o8Do
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:49:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.59  % Solved by: fo/fo7.sh
% 0.22/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.59  % done 267 iterations in 0.130s
% 0.22/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.59  % SZS output start Refutation
% 0.22/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.22/0.59  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.22/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.59  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.22/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.59  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.59  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.22/0.59  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.22/0.59  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.59  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.59  thf(t49_tex_2, conjecture,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.22/0.59         ( l1_pre_topc @ A ) ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59           ( ( v3_tex_2 @ B @ A ) <=>
% 0.22/0.59             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.22/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.59    (~( ![A:$i]:
% 0.22/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.59            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.59          ( ![B:$i]:
% 0.22/0.59            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59              ( ( v3_tex_2 @ B @ A ) <=>
% 0.22/0.59                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.22/0.59    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.22/0.59  thf('0', plain,
% 0.22/0.59      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.59        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('1', plain,
% 0.22/0.59      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.59      inference('split', [status(esa)], ['0'])).
% 0.22/0.59  thf('2', plain,
% 0.22/0.59      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.59        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('3', plain,
% 0.22/0.59      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.22/0.59       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.59      inference('split', [status(esa)], ['2'])).
% 0.22/0.59  thf('4', plain,
% 0.22/0.59      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.59      inference('split', [status(esa)], ['2'])).
% 0.22/0.59  thf('5', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(t47_tex_2, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.22/0.59             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.22/0.59  thf('6', plain,
% 0.22/0.59      (![X19 : $i, X20 : $i]:
% 0.22/0.59         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.22/0.59          | (v1_tops_1 @ X19 @ X20)
% 0.22/0.59          | ~ (v3_tex_2 @ X19 @ X20)
% 0.22/0.59          | ~ (v3_pre_topc @ X19 @ X20)
% 0.22/0.59          | ~ (l1_pre_topc @ X20)
% 0.22/0.59          | ~ (v2_pre_topc @ X20)
% 0.22/0.59          | (v2_struct_0 @ X20))),
% 0.22/0.59      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.22/0.59  thf('7', plain,
% 0.22/0.59      (((v2_struct_0 @ sk_A)
% 0.22/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.59        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.22/0.59        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.59        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.22/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.59  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('10', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(t17_tdlat_3, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.59       ( ( v1_tdlat_3 @ A ) <=>
% 0.22/0.59         ( ![B:$i]:
% 0.22/0.59           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.22/0.59  thf('11', plain,
% 0.22/0.59      (![X15 : $i, X16 : $i]:
% 0.22/0.59         (~ (v1_tdlat_3 @ X15)
% 0.22/0.59          | (v3_pre_topc @ X16 @ X15)
% 0.22/0.59          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.59          | ~ (l1_pre_topc @ X15)
% 0.22/0.59          | ~ (v2_pre_topc @ X15))),
% 0.22/0.59      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.22/0.59  thf('12', plain,
% 0.22/0.59      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.59        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.22/0.59        | ~ (v1_tdlat_3 @ sk_A))),
% 0.22/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.59  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('15', plain, ((v1_tdlat_3 @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('16', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.22/0.59      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.22/0.59  thf('17', plain,
% 0.22/0.59      (((v2_struct_0 @ sk_A)
% 0.22/0.59        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.59        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.22/0.59      inference('demod', [status(thm)], ['7', '8', '9', '16'])).
% 0.22/0.59  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('19', plain,
% 0.22/0.59      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.59      inference('clc', [status(thm)], ['17', '18'])).
% 0.22/0.59  thf('20', plain,
% 0.22/0.59      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['4', '19'])).
% 0.22/0.59  thf('21', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(d2_tops_3, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( l1_pre_topc @ A ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59           ( ( v1_tops_1 @ B @ A ) <=>
% 0.22/0.59             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.59  thf('22', plain,
% 0.22/0.59      (![X11 : $i, X12 : $i]:
% 0.22/0.59         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.59          | ~ (v1_tops_1 @ X11 @ X12)
% 0.22/0.59          | ((k2_pre_topc @ X12 @ X11) = (u1_struct_0 @ X12))
% 0.22/0.59          | ~ (l1_pre_topc @ X12))),
% 0.22/0.59      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.22/0.59  thf('23', plain,
% 0.22/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.59        | ((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.22/0.59        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.22/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.59  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('25', plain,
% 0.22/0.59      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.22/0.59        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.22/0.59      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.59  thf('26', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(t52_pre_topc, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( l1_pre_topc @ A ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.22/0.59             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.22/0.59               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.22/0.59  thf('27', plain,
% 0.22/0.59      (![X7 : $i, X8 : $i]:
% 0.22/0.59         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.59          | ~ (v4_pre_topc @ X7 @ X8)
% 0.22/0.59          | ((k2_pre_topc @ X8 @ X7) = (X7))
% 0.22/0.59          | ~ (l1_pre_topc @ X8))),
% 0.22/0.59      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.22/0.59  thf('28', plain,
% 0.22/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.59        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.22/0.59        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.59  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('30', plain,
% 0.22/0.59      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.22/0.59        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.59      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.59  thf('31', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(dt_k3_subset_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.59       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.59  thf('32', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.22/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.22/0.59      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.59  thf('33', plain,
% 0.22/0.59      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.59  thf(fc3_tops_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.22/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.59       ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ))).
% 0.22/0.59  thf('34', plain,
% 0.22/0.59      (![X9 : $i, X10 : $i]:
% 0.22/0.59         (~ (l1_pre_topc @ X9)
% 0.22/0.59          | ~ (v2_pre_topc @ X9)
% 0.22/0.59          | ~ (v3_pre_topc @ X10 @ X9)
% 0.22/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.59          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X9) @ X10) @ X9))),
% 0.22/0.59      inference('cnf', [status(esa)], [fc3_tops_1])).
% 0.22/0.59  thf('35', plain,
% 0.22/0.59      (((v4_pre_topc @ 
% 0.22/0.59         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.59          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.22/0.59         sk_A)
% 0.22/0.59        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.22/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.59  thf('36', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(involutiveness_k3_subset_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.59       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.22/0.59  thf('37', plain,
% 0.22/0.59      (![X2 : $i, X3 : $i]:
% 0.22/0.59         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 0.22/0.59          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.22/0.59      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.59  thf('38', plain,
% 0.22/0.59      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.59         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.22/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.59  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('41', plain,
% 0.22/0.59      (((v4_pre_topc @ sk_B_1 @ sk_A)
% 0.22/0.59        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.22/0.59      inference('demod', [status(thm)], ['35', '38', '39', '40'])).
% 0.22/0.59  thf('42', plain,
% 0.22/0.59      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.59  thf('43', plain,
% 0.22/0.59      (![X15 : $i, X16 : $i]:
% 0.22/0.59         (~ (v1_tdlat_3 @ X15)
% 0.22/0.59          | (v3_pre_topc @ X16 @ X15)
% 0.22/0.59          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.59          | ~ (l1_pre_topc @ X15)
% 0.22/0.59          | ~ (v2_pre_topc @ X15))),
% 0.22/0.59      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.22/0.59  thf('44', plain,
% 0.22/0.59      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.59        | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.22/0.59        | ~ (v1_tdlat_3 @ sk_A))),
% 0.22/0.59      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.59  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('47', plain, ((v1_tdlat_3 @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('48', plain,
% 0.22/0.59      ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.22/0.59      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.22/0.59  thf('49', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.22/0.59      inference('demod', [status(thm)], ['41', '48'])).
% 0.22/0.59  thf('50', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.22/0.59      inference('demod', [status(thm)], ['30', '49'])).
% 0.22/0.59  thf('51', plain,
% 0.22/0.59      ((((sk_B_1) = (u1_struct_0 @ sk_A)) | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.22/0.59      inference('demod', [status(thm)], ['25', '50'])).
% 0.22/0.59  thf('52', plain,
% 0.22/0.59      ((((sk_B_1) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['20', '51'])).
% 0.22/0.59  thf('53', plain,
% 0.22/0.59      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('split', [status(esa)], ['0'])).
% 0.22/0.59  thf('54', plain,
% 0.22/0.59      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.22/0.59         <= (((v3_tex_2 @ sk_B_1 @ sk_A)) & 
% 0.22/0.59             ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('sup+', [status(thm)], ['52', '53'])).
% 0.22/0.59  thf('55', plain,
% 0.22/0.59      ((((sk_B_1) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['20', '51'])).
% 0.22/0.59  thf(fc12_struct_0, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( l1_struct_0 @ A ) =>
% 0.22/0.59       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.59  thf('56', plain,
% 0.22/0.59      (![X6 : $i]:
% 0.22/0.59         (~ (v1_subset_1 @ (k2_struct_0 @ X6) @ (u1_struct_0 @ X6))
% 0.22/0.59          | ~ (l1_struct_0 @ X6))),
% 0.22/0.59      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.22/0.59  thf('57', plain,
% 0.22/0.59      (((~ (v1_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1)
% 0.22/0.59         | ~ (l1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.59  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(dt_l1_pre_topc, axiom,
% 0.22/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.59  thf('59', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.22/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.59  thf('60', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.59      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.59  thf('61', plain,
% 0.22/0.59      ((~ (v1_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.22/0.59         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.59      inference('demod', [status(thm)], ['57', '60'])).
% 0.22/0.59  thf(d3_struct_0, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.22/0.59  thf('62', plain,
% 0.22/0.59      (![X4 : $i]:
% 0.22/0.59         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.22/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.59  thf('63', plain,
% 0.22/0.59      ((((sk_B_1) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['20', '51'])).
% 0.22/0.59  thf('64', plain,
% 0.22/0.59      (((((sk_B_1) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.22/0.59         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.59      inference('sup+', [status(thm)], ['62', '63'])).
% 0.22/0.59  thf('65', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.59      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.59  thf('66', plain,
% 0.22/0.59      ((((sk_B_1) = (k2_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.59      inference('demod', [status(thm)], ['64', '65'])).
% 0.22/0.59  thf('67', plain,
% 0.22/0.59      ((~ (v1_subset_1 @ sk_B_1 @ sk_B_1)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.22/0.59      inference('demod', [status(thm)], ['61', '66'])).
% 0.22/0.59  thf('68', plain,
% 0.22/0.59      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.22/0.59       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['54', '67'])).
% 0.22/0.59  thf('69', plain,
% 0.22/0.59      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.22/0.59       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('split', [status(esa)], ['0'])).
% 0.22/0.59  thf('70', plain, (~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.59      inference('sat_resolution*', [status(thm)], ['3', '68', '69'])).
% 0.22/0.59  thf('71', plain, (~ (v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.22/0.59      inference('simpl_trail', [status(thm)], ['1', '70'])).
% 0.22/0.59  thf('72', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(t48_tex_2, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.22/0.59             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.22/0.59  thf('73', plain,
% 0.22/0.59      (![X21 : $i, X22 : $i]:
% 0.22/0.59         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.22/0.59          | (v3_tex_2 @ X21 @ X22)
% 0.22/0.59          | ~ (v2_tex_2 @ X21 @ X22)
% 0.22/0.59          | ~ (v1_tops_1 @ X21 @ X22)
% 0.22/0.59          | ~ (l1_pre_topc @ X22)
% 0.22/0.59          | ~ (v2_pre_topc @ X22)
% 0.22/0.59          | (v2_struct_0 @ X22))),
% 0.22/0.59      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.22/0.59  thf('74', plain,
% 0.22/0.59      (((v2_struct_0 @ sk_A)
% 0.22/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.59        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.22/0.59        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.59        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.59      inference('sup-', [status(thm)], ['72', '73'])).
% 0.22/0.59  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('77', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(t43_tex_2, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.22/0.59         ( l1_pre_topc @ A ) ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.59           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.22/0.59  thf('78', plain,
% 0.22/0.59      (![X17 : $i, X18 : $i]:
% 0.22/0.59         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.59          | (v2_tex_2 @ X17 @ X18)
% 0.22/0.59          | ~ (l1_pre_topc @ X18)
% 0.22/0.59          | ~ (v1_tdlat_3 @ X18)
% 0.22/0.59          | ~ (v2_pre_topc @ X18)
% 0.22/0.59          | (v2_struct_0 @ X18))),
% 0.22/0.59      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.22/0.59  thf('79', plain,
% 0.22/0.59      (((v2_struct_0 @ sk_A)
% 0.22/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.59        | ~ (v1_tdlat_3 @ sk_A)
% 0.22/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.59        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.59      inference('sup-', [status(thm)], ['77', '78'])).
% 0.22/0.59  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('81', plain, ((v1_tdlat_3 @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('83', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.59      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 0.22/0.59  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('85', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.22/0.59      inference('clc', [status(thm)], ['83', '84'])).
% 0.22/0.59  thf('86', plain,
% 0.22/0.59      (((v2_struct_0 @ sk_A)
% 0.22/0.59        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.22/0.59        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.59      inference('demod', [status(thm)], ['74', '75', '76', '85'])).
% 0.22/0.59  thf('87', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(d7_subset_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.59       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.22/0.59  thf('88', plain,
% 0.22/0.59      (![X13 : $i, X14 : $i]:
% 0.22/0.59         (((X14) = (X13))
% 0.22/0.59          | (v1_subset_1 @ X14 @ X13)
% 0.22/0.59          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.22/0.59      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.22/0.59  thf('89', plain,
% 0.22/0.59      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.59        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['87', '88'])).
% 0.22/0.59  thf('90', plain,
% 0.22/0.59      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('split', [status(esa)], ['2'])).
% 0.22/0.59  thf('91', plain,
% 0.22/0.59      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['89', '90'])).
% 0.22/0.59  thf('92', plain,
% 0.22/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('93', plain,
% 0.22/0.59      (((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_B_1)))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('sup+', [status(thm)], ['91', '92'])).
% 0.22/0.59  thf('94', plain,
% 0.22/0.59      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['89', '90'])).
% 0.22/0.59  thf('95', plain,
% 0.22/0.59      (![X11 : $i, X12 : $i]:
% 0.22/0.59         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.59          | ((k2_pre_topc @ X12 @ X11) != (u1_struct_0 @ X12))
% 0.22/0.59          | (v1_tops_1 @ X11 @ X12)
% 0.22/0.59          | ~ (l1_pre_topc @ X12))),
% 0.22/0.59      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.22/0.59  thf('96', plain,
% 0.22/0.59      ((![X0 : $i]:
% 0.22/0.59          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.22/0.59           | ~ (l1_pre_topc @ sk_A)
% 0.22/0.59           | (v1_tops_1 @ X0 @ sk_A)
% 0.22/0.59           | ((k2_pre_topc @ sk_A @ X0) != (u1_struct_0 @ sk_A))))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['94', '95'])).
% 0.22/0.59  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('98', plain,
% 0.22/0.59      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['89', '90'])).
% 0.22/0.59  thf('99', plain,
% 0.22/0.59      ((![X0 : $i]:
% 0.22/0.59          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.22/0.59           | (v1_tops_1 @ X0 @ sk_A)
% 0.22/0.59           | ((k2_pre_topc @ sk_A @ X0) != (sk_B_1))))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.22/0.59  thf('100', plain,
% 0.22/0.59      (((((k2_pre_topc @ sk_A @ sk_B_1) != (sk_B_1))
% 0.22/0.59         | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['93', '99'])).
% 0.22/0.59  thf('101', plain,
% 0.22/0.59      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['89', '90'])).
% 0.22/0.59  thf('102', plain,
% 0.22/0.59      (((v4_pre_topc @ sk_B_1 @ sk_A)
% 0.22/0.59        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.22/0.59      inference('demod', [status(thm)], ['35', '38', '39', '40'])).
% 0.22/0.59  thf('103', plain,
% 0.22/0.59      (((~ (v3_pre_topc @ (k3_subset_1 @ sk_B_1 @ sk_B_1) @ sk_A)
% 0.22/0.59         | (v4_pre_topc @ sk_B_1 @ sk_A)))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['101', '102'])).
% 0.22/0.59  thf('104', plain,
% 0.22/0.59      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['89', '90'])).
% 0.22/0.59  thf('105', plain,
% 0.22/0.59      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.59  thf('106', plain,
% 0.22/0.59      (((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.22/0.59         (k1_zfmisc_1 @ sk_B_1)))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('sup+', [status(thm)], ['104', '105'])).
% 0.22/0.59  thf('107', plain,
% 0.22/0.59      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['89', '90'])).
% 0.22/0.59  thf('108', plain,
% 0.22/0.59      (((m1_subset_1 @ (k3_subset_1 @ sk_B_1 @ sk_B_1) @ (k1_zfmisc_1 @ sk_B_1)))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('demod', [status(thm)], ['106', '107'])).
% 0.22/0.59  thf('109', plain,
% 0.22/0.59      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['89', '90'])).
% 0.22/0.59  thf('110', plain,
% 0.22/0.59      (![X15 : $i, X16 : $i]:
% 0.22/0.59         (~ (v1_tdlat_3 @ X15)
% 0.22/0.59          | (v3_pre_topc @ X16 @ X15)
% 0.22/0.59          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.59          | ~ (l1_pre_topc @ X15)
% 0.22/0.59          | ~ (v2_pre_topc @ X15))),
% 0.22/0.59      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.22/0.59  thf('111', plain,
% 0.22/0.59      ((![X0 : $i]:
% 0.22/0.59          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.22/0.59           | ~ (v2_pre_topc @ sk_A)
% 0.22/0.59           | ~ (l1_pre_topc @ sk_A)
% 0.22/0.59           | (v3_pre_topc @ X0 @ sk_A)
% 0.22/0.59           | ~ (v1_tdlat_3 @ sk_A)))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['109', '110'])).
% 0.22/0.59  thf('112', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('114', plain, ((v1_tdlat_3 @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('115', plain,
% 0.22/0.59      ((![X0 : $i]:
% 0.22/0.59          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.22/0.59           | (v3_pre_topc @ X0 @ sk_A)))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 0.22/0.59  thf('116', plain,
% 0.22/0.59      (((v3_pre_topc @ (k3_subset_1 @ sk_B_1 @ sk_B_1) @ sk_A))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['108', '115'])).
% 0.22/0.59  thf('117', plain,
% 0.22/0.59      (((v4_pre_topc @ sk_B_1 @ sk_A))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('demod', [status(thm)], ['103', '116'])).
% 0.22/0.59  thf('118', plain,
% 0.22/0.59      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.22/0.59        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.59      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.59  thf('119', plain,
% 0.22/0.59      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['117', '118'])).
% 0.22/0.59  thf('120', plain,
% 0.22/0.59      (((((sk_B_1) != (sk_B_1)) | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('demod', [status(thm)], ['100', '119'])).
% 0.22/0.59  thf('121', plain,
% 0.22/0.59      (((v1_tops_1 @ sk_B_1 @ sk_A))
% 0.22/0.59         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.59      inference('simplify', [status(thm)], ['120'])).
% 0.22/0.59  thf('122', plain, (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.59      inference('sat_resolution*', [status(thm)], ['3', '68'])).
% 0.22/0.59  thf('123', plain, ((v1_tops_1 @ sk_B_1 @ sk_A)),
% 0.22/0.59      inference('simpl_trail', [status(thm)], ['121', '122'])).
% 0.22/0.59  thf('124', plain, (((v2_struct_0 @ sk_A) | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.22/0.59      inference('demod', [status(thm)], ['86', '123'])).
% 0.22/0.59  thf('125', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('126', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.22/0.59      inference('clc', [status(thm)], ['124', '125'])).
% 0.22/0.59  thf('127', plain, ($false), inference('demod', [status(thm)], ['71', '126'])).
% 0.22/0.59  
% 0.22/0.59  % SZS output end Refutation
% 0.22/0.59  
% 0.44/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
