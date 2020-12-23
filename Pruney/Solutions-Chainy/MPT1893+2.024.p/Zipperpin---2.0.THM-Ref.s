%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3eohO6eYHd

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:37 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 300 expanded)
%              Number of leaves         :   27 (  95 expanded)
%              Depth                    :   17
%              Number of atoms          :  755 (4219 expanded)
%              Number of equality atoms :   23 (  46 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v4_pre_topc @ X6 @ X7 )
      | ( ( k2_pre_topc @ X7 @ X6 )
        = X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v1_tops_1 @ X14 @ X15 )
      | ~ ( v3_tex_2 @ X14 @ X15 )
      | ~ ( v3_pre_topc @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v1_tops_1 @ X10 @ X11 )
      | ( ( k2_pre_topc @ X11 @ X10 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_tdlat_3 @ X12 )
      | ~ ( v4_pre_topc @ X13 @ X12 )
      | ( v3_pre_topc @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
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

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('43',plain,(
    ! [X5: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('45',plain,(
    ! [X5: $i] :
      ~ ( v1_subset_1 @ X5 @ X5 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('48',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['23','48'])).

thf('50',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['5','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('52',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X9 ) @ X8 ) @ X9 )
      | ( v4_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('57',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('58',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_tdlat_3 @ X12 )
      | ~ ( v4_pre_topc @ X13 @ X12 )
      | ( v3_pre_topc @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('60',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('66',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('67',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X9 ) @ X8 ) @ X9 )
      | ( v4_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('71',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X4 @ ( k3_subset_1 @ X4 @ X3 ) )
        = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('72',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','72'])).

thf('74',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','73'])).

thf('75',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('76',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['74','75'])).

thf('77',plain,(
    v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['64','76'])).

thf('78',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['55','77'])).

thf('79',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['50','78'])).

thf('80',plain,(
    v1_subset_1 @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['0','79'])).

thf('81',plain,(
    ! [X5: $i] :
      ~ ( v1_subset_1 @ X5 @ X5 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('82',plain,(
    $false ),
    inference('sup-',[status(thm)],['80','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3eohO6eYHd
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:00:48 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.34/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.53  % Solved by: fo/fo7.sh
% 0.34/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.53  % done 135 iterations in 0.071s
% 0.34/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.53  % SZS output start Refutation
% 0.34/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.34/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.34/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.34/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.34/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.34/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.34/0.53  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.34/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.34/0.53  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.34/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.34/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.34/0.53  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.34/0.53  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.34/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.34/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.53  thf(t61_tex_2, conjecture,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.34/0.53         ( l1_pre_topc @ A ) ) =>
% 0.34/0.53       ( ![B:$i]:
% 0.34/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.53           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.34/0.53                ( v3_tex_2 @ B @ A ) & 
% 0.34/0.53                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.34/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.53    (~( ![A:$i]:
% 0.34/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.34/0.53            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.53          ( ![B:$i]:
% 0.34/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.53              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.34/0.53                   ( v3_tex_2 @ B @ A ) & 
% 0.34/0.53                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.34/0.53    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 0.34/0.53  thf('0', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('1', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t52_pre_topc, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( l1_pre_topc @ A ) =>
% 0.34/0.53       ( ![B:$i]:
% 0.34/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.53           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.34/0.53             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.34/0.53               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.34/0.53  thf('2', plain,
% 0.34/0.53      (![X6 : $i, X7 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.34/0.53          | ~ (v4_pre_topc @ X6 @ X7)
% 0.34/0.53          | ((k2_pre_topc @ X7 @ X6) = (X6))
% 0.34/0.53          | ~ (l1_pre_topc @ X7))),
% 0.34/0.53      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.34/0.53  thf('3', plain,
% 0.34/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.34/0.53        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.34/0.53        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.34/0.53  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('5', plain,
% 0.34/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.34/0.53        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.34/0.53  thf('6', plain,
% 0.34/0.53      (((v3_pre_topc @ sk_B_1 @ sk_A) | (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('7', plain,
% 0.34/0.53      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.34/0.53      inference('split', [status(esa)], ['6'])).
% 0.34/0.53  thf('8', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t47_tex_2, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.53       ( ![B:$i]:
% 0.34/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.53           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.34/0.53             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.34/0.53  thf('9', plain,
% 0.34/0.53      (![X14 : $i, X15 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.34/0.53          | (v1_tops_1 @ X14 @ X15)
% 0.34/0.53          | ~ (v3_tex_2 @ X14 @ X15)
% 0.34/0.53          | ~ (v3_pre_topc @ X14 @ X15)
% 0.34/0.53          | ~ (l1_pre_topc @ X15)
% 0.34/0.53          | ~ (v2_pre_topc @ X15)
% 0.34/0.53          | (v2_struct_0 @ X15))),
% 0.34/0.53      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.34/0.53  thf('10', plain,
% 0.34/0.53      (((v2_struct_0 @ sk_A)
% 0.34/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.34/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.34/0.53        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.34/0.53        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.34/0.53        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.34/0.53  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('13', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('14', plain,
% 0.34/0.53      (((v2_struct_0 @ sk_A)
% 0.34/0.53        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.34/0.53        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.34/0.53  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('16', plain,
% 0.34/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('clc', [status(thm)], ['14', '15'])).
% 0.34/0.53  thf('17', plain,
% 0.34/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['7', '16'])).
% 0.34/0.53  thf('18', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(d2_tops_3, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( l1_pre_topc @ A ) =>
% 0.34/0.53       ( ![B:$i]:
% 0.34/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.53           ( ( v1_tops_1 @ B @ A ) <=>
% 0.34/0.53             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.34/0.53  thf('19', plain,
% 0.34/0.53      (![X10 : $i, X11 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.34/0.53          | ~ (v1_tops_1 @ X10 @ X11)
% 0.34/0.53          | ((k2_pre_topc @ X11 @ X10) = (u1_struct_0 @ X11))
% 0.34/0.53          | ~ (l1_pre_topc @ X11))),
% 0.34/0.53      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.34/0.53  thf('20', plain,
% 0.34/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.34/0.53        | ((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.34/0.53        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.34/0.53  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('22', plain,
% 0.34/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.34/0.53        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.34/0.53  thf('23', plain,
% 0.34/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.34/0.53         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['17', '22'])).
% 0.34/0.53  thf('24', plain,
% 0.34/0.53      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.34/0.53      inference('split', [status(esa)], ['6'])).
% 0.34/0.53  thf('25', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t24_tdlat_3, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.53       ( ( v3_tdlat_3 @ A ) <=>
% 0.34/0.53         ( ![B:$i]:
% 0.34/0.53           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.53             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.34/0.53  thf('26', plain,
% 0.34/0.53      (![X12 : $i, X13 : $i]:
% 0.34/0.53         (~ (v3_tdlat_3 @ X12)
% 0.34/0.53          | ~ (v4_pre_topc @ X13 @ X12)
% 0.34/0.53          | (v3_pre_topc @ X13 @ X12)
% 0.34/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.34/0.53          | ~ (l1_pre_topc @ X12)
% 0.34/0.53          | ~ (v2_pre_topc @ X12))),
% 0.34/0.53      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.34/0.53  thf('27', plain,
% 0.34/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.34/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.34/0.53        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.34/0.53        | ~ (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.34/0.53        | ~ (v3_tdlat_3 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.34/0.53  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('30', plain, ((v3_tdlat_3 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('31', plain,
% 0.34/0.53      (((v3_pre_topc @ sk_B_1 @ sk_A) | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.34/0.53  thf('32', plain,
% 0.34/0.53      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['24', '31'])).
% 0.34/0.53  thf('33', plain,
% 0.34/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('clc', [status(thm)], ['14', '15'])).
% 0.34/0.53  thf('34', plain,
% 0.34/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.34/0.53  thf('35', plain,
% 0.34/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.34/0.53        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.34/0.53  thf('36', plain,
% 0.34/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.34/0.53         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.34/0.53  thf('37', plain,
% 0.34/0.53      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.34/0.53      inference('split', [status(esa)], ['6'])).
% 0.34/0.53  thf('38', plain,
% 0.34/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.34/0.53        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.34/0.53  thf('39', plain,
% 0.34/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.34/0.53         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.34/0.53  thf('40', plain,
% 0.34/0.53      ((((u1_struct_0 @ sk_A) = (sk_B_1))) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.34/0.53      inference('sup+', [status(thm)], ['36', '39'])).
% 0.34/0.53  thf('41', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('42', plain,
% 0.34/0.53      (((v1_subset_1 @ sk_B_1 @ sk_B_1)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.34/0.53      inference('sup+', [status(thm)], ['40', '41'])).
% 0.34/0.53  thf(fc14_subset_1, axiom,
% 0.34/0.53    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.34/0.53  thf('43', plain, (![X5 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X5) @ X5)),
% 0.34/0.53      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.34/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.34/0.53  thf('44', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.34/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.34/0.53  thf('45', plain, (![X5 : $i]: ~ (v1_subset_1 @ X5 @ X5)),
% 0.34/0.53      inference('demod', [status(thm)], ['43', '44'])).
% 0.34/0.53  thf('46', plain, (~ ((v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['42', '45'])).
% 0.34/0.53  thf('47', plain,
% 0.34/0.53      (((v3_pre_topc @ sk_B_1 @ sk_A)) | ((v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('split', [status(esa)], ['6'])).
% 0.34/0.53  thf('48', plain, (((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 0.34/0.53  thf('49', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.34/0.53      inference('simpl_trail', [status(thm)], ['23', '48'])).
% 0.34/0.53  thf('50', plain,
% 0.34/0.53      ((((u1_struct_0 @ sk_A) = (sk_B_1)) | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['5', '49'])).
% 0.34/0.53  thf('51', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t29_tops_1, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( l1_pre_topc @ A ) =>
% 0.34/0.53       ( ![B:$i]:
% 0.34/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.53           ( ( v4_pre_topc @ B @ A ) <=>
% 0.34/0.53             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.34/0.53  thf('52', plain,
% 0.34/0.53      (![X8 : $i, X9 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.34/0.53          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X9) @ X8) @ X9)
% 0.34/0.53          | (v4_pre_topc @ X8 @ X9)
% 0.34/0.53          | ~ (l1_pre_topc @ X9))),
% 0.34/0.53      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.34/0.53  thf('53', plain,
% 0.34/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.34/0.53        | (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.34/0.53        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.34/0.53  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('55', plain,
% 0.34/0.53      (((v4_pre_topc @ sk_B_1 @ sk_A)
% 0.34/0.53        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['53', '54'])).
% 0.34/0.53  thf('56', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(dt_k3_subset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.53       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.34/0.53  thf('57', plain,
% 0.34/0.53      (![X1 : $i, X2 : $i]:
% 0.34/0.53         ((m1_subset_1 @ (k3_subset_1 @ X1 @ X2) @ (k1_zfmisc_1 @ X1))
% 0.34/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.34/0.53  thf('58', plain,
% 0.34/0.53      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.34/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.34/0.53  thf('59', plain,
% 0.34/0.53      (![X12 : $i, X13 : $i]:
% 0.34/0.53         (~ (v3_tdlat_3 @ X12)
% 0.34/0.53          | ~ (v4_pre_topc @ X13 @ X12)
% 0.34/0.53          | (v3_pre_topc @ X13 @ X12)
% 0.34/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.34/0.53          | ~ (l1_pre_topc @ X12)
% 0.34/0.53          | ~ (v2_pre_topc @ X12))),
% 0.34/0.53      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.34/0.53  thf('60', plain,
% 0.34/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.34/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.34/0.53        | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.34/0.53        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.34/0.53        | ~ (v3_tdlat_3 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['58', '59'])).
% 0.34/0.53  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('63', plain, ((v3_tdlat_3 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('64', plain,
% 0.34/0.53      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.34/0.53        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.34/0.53  thf('65', plain,
% 0.34/0.53      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.34/0.53      inference('split', [status(esa)], ['6'])).
% 0.34/0.53  thf('66', plain,
% 0.34/0.53      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.34/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.34/0.53  thf('67', plain,
% 0.34/0.53      (![X8 : $i, X9 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.34/0.53          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X9) @ X8) @ X9)
% 0.34/0.53          | (v4_pre_topc @ X8 @ X9)
% 0.34/0.53          | ~ (l1_pre_topc @ X9))),
% 0.34/0.53      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.34/0.53  thf('68', plain,
% 0.34/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.34/0.53        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.34/0.53        | ~ (v3_pre_topc @ 
% 0.34/0.53             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.53              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.34/0.53             sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['66', '67'])).
% 0.34/0.53  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('70', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(involutiveness_k3_subset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.53       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.34/0.53  thf('71', plain,
% 0.34/0.53      (![X3 : $i, X4 : $i]:
% 0.34/0.53         (((k3_subset_1 @ X4 @ (k3_subset_1 @ X4 @ X3)) = (X3))
% 0.34/0.53          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.34/0.53      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.34/0.53  thf('72', plain,
% 0.34/0.53      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.53         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.34/0.53      inference('sup-', [status(thm)], ['70', '71'])).
% 0.34/0.53  thf('73', plain,
% 0.34/0.53      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.34/0.53        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['68', '69', '72'])).
% 0.34/0.53  thf('74', plain,
% 0.34/0.53      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))
% 0.34/0.53         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['65', '73'])).
% 0.34/0.53  thf('75', plain, (((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.34/0.53      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 0.34/0.53  thf('76', plain,
% 0.34/0.53      ((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.34/0.53      inference('simpl_trail', [status(thm)], ['74', '75'])).
% 0.34/0.53  thf('77', plain,
% 0.34/0.53      ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.34/0.53      inference('demod', [status(thm)], ['64', '76'])).
% 0.34/0.53  thf('78', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.34/0.53      inference('demod', [status(thm)], ['55', '77'])).
% 0.34/0.53  thf('79', plain, (((u1_struct_0 @ sk_A) = (sk_B_1))),
% 0.34/0.53      inference('demod', [status(thm)], ['50', '78'])).
% 0.34/0.53  thf('80', plain, ((v1_subset_1 @ sk_B_1 @ sk_B_1)),
% 0.34/0.53      inference('demod', [status(thm)], ['0', '79'])).
% 0.34/0.53  thf('81', plain, (![X5 : $i]: ~ (v1_subset_1 @ X5 @ X5)),
% 0.34/0.53      inference('demod', [status(thm)], ['43', '44'])).
% 0.34/0.53  thf('82', plain, ($false), inference('sup-', [status(thm)], ['80', '81'])).
% 0.34/0.53  
% 0.34/0.53  % SZS output end Refutation
% 0.34/0.53  
% 0.34/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
