%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6oiMvNWicW

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 315 expanded)
%              Number of leaves         :   28 (  98 expanded)
%              Depth                    :   17
%              Number of atoms          :  802 (4360 expanded)
%              Number of equality atoms :   25 (  52 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v4_pre_topc @ X10 @ X11 )
      | ( ( k2_pre_topc @ X11 @ X10 )
        = X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_tops_1 @ X20 @ X21 )
      | ~ ( v3_tex_2 @ X20 @ X21 )
      | ~ ( v3_pre_topc @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v1_tops_1 @ X14 @ X15 )
      | ( ( k2_pre_topc @ X15 @ X14 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v3_tdlat_3 @ X18 )
      | ~ ( v4_pre_topc @ X19 @ X18 )
      | ( v3_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('27',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('34',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('36',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('38',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('39',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_subset_1 @ X17 @ X16 )
      | ( X17 != X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('44',plain,(
    ! [X16: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( v1_subset_1 @ X16 @ X16 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['45'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('47',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X16: $i] :
      ~ ( v1_subset_1 @ X16 @ X16 ) ),
    inference(demod,[status(thm)],['44','48'])).

thf('50',plain,(
    ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('52',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['23','52'])).

thf('54',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('56',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 ) @ X13 )
      | ( v4_pre_topc @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('61',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('62',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v3_tdlat_3 @ X18 )
      | ~ ( v4_pre_topc @ X19 @ X18 )
      | ( v3_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('64',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('70',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('71',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 ) @ X13 )
      | ( v4_pre_topc @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('72',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('75',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('76',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','76'])).

thf('78',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','77'])).

thf('79',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('80',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['78','79'])).

thf('81',plain,(
    v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['68','80'])).

thf('82',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['59','81'])).

thf('83',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['54','82'])).

thf('84',plain,(
    v1_subset_1 @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['0','83'])).

thf('85',plain,(
    ! [X16: $i] :
      ~ ( v1_subset_1 @ X16 @ X16 ) ),
    inference(demod,[status(thm)],['44','48'])).

thf('86',plain,(
    $false ),
    inference('sup-',[status(thm)],['84','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6oiMvNWicW
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:00:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 155 iterations in 0.066s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.52  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.52  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
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
% 0.20/0.52  thf('0', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t52_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.52             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.52               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.52          | ~ (v4_pre_topc @ X10 @ X11)
% 0.20/0.52          | ((k2_pre_topc @ X11 @ X10) = (X10))
% 0.20/0.52          | ~ (l1_pre_topc @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.20/0.52        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.20/0.52        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (((v3_pre_topc @ sk_B_1 @ sk_A) | (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['6'])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t47_tex_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.20/0.52             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.52          | (v1_tops_1 @ X20 @ X21)
% 0.20/0.52          | ~ (v3_tex_2 @ X20 @ X21)
% 0.20/0.52          | ~ (v3_pre_topc @ X20 @ X21)
% 0.20/0.52          | ~ (l1_pre_topc @ X21)
% 0.20/0.52          | ~ (v2_pre_topc @ X21)
% 0.20/0.52          | (v2_struct_0 @ X21))),
% 0.20/0.52      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.52        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.52        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('13', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.52        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.20/0.52  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d2_tops_3, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( v1_tops_1 @ B @ A ) <=>
% 0.20/0.52             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X14 : $i, X15 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.52          | ~ (v1_tops_1 @ X14 @ X15)
% 0.20/0.52          | ((k2_pre_topc @ X15 @ X14) = (u1_struct_0 @ X15))
% 0.20/0.52          | ~ (l1_pre_topc @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.20/0.52        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.20/0.52        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.52         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['6'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t24_tdlat_3, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ( v3_tdlat_3 @ A ) <=>
% 0.20/0.52         ( ![B:$i]:
% 0.20/0.52           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X18 : $i, X19 : $i]:
% 0.20/0.52         (~ (v3_tdlat_3 @ X18)
% 0.20/0.52          | ~ (v4_pre_topc @ X19 @ X18)
% 0.20/0.52          | (v3_pre_topc @ X19 @ X18)
% 0.20/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.52          | ~ (l1_pre_topc @ X18)
% 0.20/0.52          | ~ (v2_pre_topc @ X18))),
% 0.20/0.52      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.52        | ~ (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.52        | ~ (v3_tdlat_3 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.52  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('30', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (((v3_pre_topc @ sk_B_1 @ sk_A) | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.20/0.52        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.52         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['6'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.20/0.52        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.20/0.52         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      ((((u1_struct_0 @ sk_A) = (sk_B_1))) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['36', '39'])).
% 0.20/0.52  thf('41', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (((v1_subset_1 @ sk_B_1 @ sk_B_1)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['40', '41'])).
% 0.20/0.52  thf(d7_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i]:
% 0.20/0.52         (~ (v1_subset_1 @ X17 @ X16)
% 0.20/0.52          | ((X17) != (X16))
% 0.20/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X16 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X16))
% 0.20/0.52          | ~ (v1_subset_1 @ X16 @ X16))),
% 0.20/0.52      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.52  thf(d10_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('46', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.52      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.52  thf(t3_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X7 : $i, X9 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.52  thf('48', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.52  thf('49', plain, (![X16 : $i]: ~ (v1_subset_1 @ X16 @ X16)),
% 0.20/0.52      inference('demod', [status(thm)], ['44', '48'])).
% 0.20/0.52  thf('50', plain, (~ ((v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['42', '49'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (((v3_pre_topc @ sk_B_1 @ sk_A)) | ((v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('split', [status(esa)], ['6'])).
% 0.20/0.52  thf('52', plain, (((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 0.20/0.52  thf('53', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['23', '52'])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      ((((u1_struct_0 @ sk_A) = (sk_B_1)) | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['5', '53'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t29_tops_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.52             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.52          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X13) @ X12) @ X13)
% 0.20/0.52          | (v4_pre_topc @ X12 @ X13)
% 0.20/0.52          | ~ (l1_pre_topc @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.52        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.52  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      (((v4_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.52        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.52  thf('60', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_k3_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 0.20/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      (![X18 : $i, X19 : $i]:
% 0.20/0.52         (~ (v3_tdlat_3 @ X18)
% 0.20/0.52          | ~ (v4_pre_topc @ X19 @ X18)
% 0.20/0.52          | (v3_pre_topc @ X19 @ X18)
% 0.20/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.52          | ~ (l1_pre_topc @ X18)
% 0.20/0.52          | ~ (v2_pre_topc @ X18))),
% 0.20/0.52      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.20/0.52        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.20/0.52        | ~ (v3_tdlat_3 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.52  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('67', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('68', plain,
% 0.20/0.52      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.20/0.52        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['6'])).
% 0.20/0.52  thf('70', plain,
% 0.20/0.52      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.52  thf('71', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.52          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X13) @ X12) @ X13)
% 0.20/0.52          | (v4_pre_topc @ X12 @ X13)
% 0.20/0.52          | ~ (l1_pre_topc @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.20/0.52        | ~ (v3_pre_topc @ 
% 0.20/0.52             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.20/0.52             sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.52  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('74', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.52  thf('75', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i]:
% 0.20/0.52         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 0.20/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.52      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.52  thf('76', plain,
% 0.20/0.52      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.52  thf('77', plain,
% 0.20/0.52      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.20/0.52        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['72', '73', '76'])).
% 0.20/0.52  thf('78', plain,
% 0.20/0.52      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))
% 0.20/0.52         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['69', '77'])).
% 0.20/0.52  thf('79', plain, (((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 0.20/0.52  thf('80', plain,
% 0.20/0.52      ((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['78', '79'])).
% 0.20/0.52  thf('81', plain,
% 0.20/0.52      ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['68', '80'])).
% 0.20/0.52  thf('82', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['59', '81'])).
% 0.20/0.52  thf('83', plain, (((u1_struct_0 @ sk_A) = (sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['54', '82'])).
% 0.20/0.52  thf('84', plain, ((v1_subset_1 @ sk_B_1 @ sk_B_1)),
% 0.20/0.52      inference('demod', [status(thm)], ['0', '83'])).
% 0.20/0.52  thf('85', plain, (![X16 : $i]: ~ (v1_subset_1 @ X16 @ X16)),
% 0.20/0.52      inference('demod', [status(thm)], ['44', '48'])).
% 0.20/0.52  thf('86', plain, ($false), inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
