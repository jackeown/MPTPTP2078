%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R579FLIdtr

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 457 expanded)
%              Number of leaves         :   34 ( 141 expanded)
%              Depth                    :   16
%              Number of atoms          : 1129 (5463 expanded)
%              Number of equality atoms :   38 (  87 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

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
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v1_tops_1 @ X22 @ X23 )
      | ~ ( v3_tex_2 @ X22 @ X23 )
      | ~ ( v3_pre_topc @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_tdlat_3 @ X18 )
      | ( v3_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v1_tops_1 @ X14 @ X15 )
      | ( ( k2_pre_topc @ X15 @ X14 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v4_pre_topc @ X9 @ X10 )
      | ( ( k2_pre_topc @ X10 @ X9 )
        = X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
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

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_tdlat_3 @ X18 )
      | ( v3_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 ) @ X12 )
      | ( v4_pre_topc @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('42',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','42'])).

thf('44',plain,
    ( ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['30','48'])).

thf('50',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','49'])).

thf('51',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','50'])).

thf('52',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('54',plain,(
    ! [X5: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('55',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('56',plain,(
    ! [X5: $i] :
      ~ ( v1_subset_1 @ X5 @ X5 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','57','58'])).

thf('60',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','59'])).

thf('61',plain,(
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

thf('62',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v3_tex_2 @ X24 @ X25 )
      | ~ ( v2_tex_2 @ X24 @ X25 )
      | ~ ( v1_tops_1 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
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

thf('67',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_tdlat_3 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('77',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17 = X16 )
      | ( v1_subset_1 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('78',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('80',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('84',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k2_pre_topc @ X15 @ X14 )
       != ( u1_struct_0 @ X15 ) )
      | ( v1_tops_1 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
       != sk_B_1 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','88'])).

thf('90',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('91',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('92',plain,
    ( ( ( k3_subset_1 @ sk_B_1 @ sk_B_1 )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('94',plain,
    ( ( ( k3_subset_1 @ sk_B_1 @ sk_B_1 )
      = ( k4_xboole_0 @ sk_B_1 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('96',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 ) @ X12 )
      | ( v4_pre_topc @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( v3_pre_topc @ ( k3_subset_1 @ sk_B_1 @ X0 ) @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ sk_B_1 @ sk_B_1 ) @ sk_A )
      | ( v4_pre_topc @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('103',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('104',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_tdlat_3 @ X18 )
      | ( v3_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( v1_tdlat_3 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( v3_pre_topc @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,
    ( ! [X0: $i] :
        ( v3_pre_topc @ ( k4_xboole_0 @ sk_B_1 @ X0 ) @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','109'])).

thf('111',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('112',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','110','111'])).

thf('113',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('114',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','114'])).

thf('116',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','57'])).

thf('118',plain,(
    v1_tops_1 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['75','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    $false ),
    inference(demod,[status(thm)],['60','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R579FLIdtr
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 146 iterations in 0.072s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.53  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.53  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.53  thf(t49_tex_2, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.20/0.53         ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( v3_tex_2 @ B @ A ) <=>
% 0.20/0.53             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.53            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53              ( ( v3_tex_2 @ B @ A ) <=>
% 0.20/0.53                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.20/0.53       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('split', [status(esa)], ['2'])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['2'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t47_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.20/0.53             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.20/0.53          | (v1_tops_1 @ X22 @ X23)
% 0.20/0.53          | ~ (v3_tex_2 @ X22 @ X23)
% 0.20/0.53          | ~ (v3_pre_topc @ X22 @ X23)
% 0.20/0.53          | ~ (l1_pre_topc @ X23)
% 0.20/0.53          | ~ (v2_pre_topc @ X23)
% 0.20/0.53          | (v2_struct_0 @ X23))),
% 0.20/0.53      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.53        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.53        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t17_tdlat_3, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ( v1_tdlat_3 @ A ) <=>
% 0.20/0.53         ( ![B:$i]:
% 0.20/0.53           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i]:
% 0.20/0.53         (~ (v1_tdlat_3 @ X18)
% 0.20/0.53          | (v3_pre_topc @ X19 @ X18)
% 0.20/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.53          | ~ (l1_pre_topc @ X18)
% 0.20/0.53          | ~ (v2_pre_topc @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.53        | ~ (v1_tdlat_3 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('15', plain, ((v1_tdlat_3 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('16', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.53        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['7', '8', '9', '16'])).
% 0.20/0.53  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d2_tops_3, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( ( v1_tops_1 @ B @ A ) <=>
% 0.20/0.54             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.54          | ~ (v1_tops_1 @ X14 @ X15)
% 0.20/0.54          | ((k2_pre_topc @ X15 @ X14) = (u1_struct_0 @ X15))
% 0.20/0.54          | ~ (l1_pre_topc @ X15))),
% 0.20/0.54      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | ((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.20/0.54        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.54  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.20/0.54        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t52_pre_topc, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.54             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.54               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X9 : $i, X10 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.54          | ~ (v4_pre_topc @ X9 @ X10)
% 0.20/0.54          | ((k2_pre_topc @ X10 @ X9) = (X9))
% 0.20/0.54          | ~ (l1_pre_topc @ X10))),
% 0.20/0.54      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.20/0.54        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.54  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.20/0.54        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.54  thf(t36_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.20/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.54  thf(t3_subset, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (![X6 : $i, X8 : $i]:
% 0.20/0.54         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i]:
% 0.20/0.54         (~ (v1_tdlat_3 @ X18)
% 0.20/0.54          | (v3_pre_topc @ X19 @ X18)
% 0.20/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.54          | ~ (l1_pre_topc @ X18)
% 0.20/0.54          | ~ (v2_pre_topc @ X18))),
% 0.20/0.54      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (v2_pre_topc @ X0)
% 0.20/0.54          | ~ (l1_pre_topc @ X0)
% 0.20/0.54          | (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.20/0.54          | ~ (v1_tdlat_3 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t29_tops_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.54             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.54          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X12) @ X11) @ X12)
% 0.20/0.54          | (v4_pre_topc @ X11 @ X12)
% 0.20/0.54          | ~ (l1_pre_topc @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.54        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.54  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d5_subset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 0.20/0.54          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.20/0.54         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (((v4_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.54        | ~ (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['38', '39', '42'])).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      ((~ (v1_tdlat_3 @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['35', '43'])).
% 0.20/0.54  thf('45', plain, ((v1_tdlat_3 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('48', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.20/0.54  thf('49', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['30', '48'])).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)) | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['25', '49'])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['20', '50'])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.20/0.54         <= (((v3_tex_2 @ sk_B_1 @ sk_A)) & 
% 0.20/0.54             ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['51', '52'])).
% 0.20/0.54  thf(fc14_subset_1, axiom,
% 0.20/0.54    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.20/0.54  thf('54', plain, (![X5 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X5) @ X5)),
% 0.20/0.54      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.20/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.54  thf('55', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.54  thf('56', plain, (![X5 : $i]: ~ (v1_subset_1 @ X5 @ X5)),
% 0.20/0.54      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.20/0.54       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['53', '56'])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.20/0.54       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('59', plain, (~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['3', '57', '58'])).
% 0.20/0.54  thf('60', plain, (~ (v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['1', '59'])).
% 0.20/0.54  thf('61', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t48_tex_2, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.20/0.54             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      (![X24 : $i, X25 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.54          | (v3_tex_2 @ X24 @ X25)
% 0.20/0.54          | ~ (v2_tex_2 @ X24 @ X25)
% 0.20/0.54          | ~ (v1_tops_1 @ X24 @ X25)
% 0.20/0.54          | ~ (l1_pre_topc @ X25)
% 0.20/0.54          | ~ (v2_pre_topc @ X25)
% 0.20/0.54          | (v2_struct_0 @ X25))),
% 0.20/0.54      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.20/0.54  thf('63', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.20/0.54        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.54        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.54  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('66', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t43_tex_2, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.20/0.54         ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.20/0.54  thf('67', plain,
% 0.20/0.54      (![X20 : $i, X21 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.54          | (v2_tex_2 @ X20 @ X21)
% 0.20/0.54          | ~ (l1_pre_topc @ X21)
% 0.20/0.54          | ~ (v1_tdlat_3 @ X21)
% 0.20/0.54          | ~ (v2_pre_topc @ X21)
% 0.20/0.54          | (v2_struct_0 @ X21))),
% 0.20/0.54      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.20/0.54  thf('68', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | ~ (v1_tdlat_3 @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.54  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('70', plain, ((v1_tdlat_3 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('72', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 0.20/0.54  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('74', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('clc', [status(thm)], ['72', '73'])).
% 0.20/0.54  thf('75', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.20/0.54        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['63', '64', '65', '74'])).
% 0.20/0.54  thf('76', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d7_subset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.54       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.20/0.54  thf('77', plain,
% 0.20/0.54      (![X16 : $i, X17 : $i]:
% 0.20/0.54         (((X17) = (X16))
% 0.20/0.54          | (v1_subset_1 @ X17 @ X16)
% 0.20/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.20/0.54  thf('78', plain,
% 0.20/0.54      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.54        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['76', '77'])).
% 0.20/0.54  thf('79', plain,
% 0.20/0.54      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('split', [status(esa)], ['2'])).
% 0.20/0.54  thf('80', plain,
% 0.20/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.54  thf('81', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('82', plain,
% 0.20/0.54      (((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_B_1)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['80', '81'])).
% 0.20/0.54  thf('83', plain,
% 0.20/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.54  thf('84', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.54          | ((k2_pre_topc @ X15 @ X14) != (u1_struct_0 @ X15))
% 0.20/0.54          | (v1_tops_1 @ X14 @ X15)
% 0.20/0.54          | ~ (l1_pre_topc @ X15))),
% 0.20/0.54      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.20/0.54  thf('85', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.20/0.54           | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54           | (v1_tops_1 @ X0 @ sk_A)
% 0.20/0.54           | ((k2_pre_topc @ sk_A @ X0) != (u1_struct_0 @ sk_A))))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.54  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('87', plain,
% 0.20/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.54  thf('88', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.20/0.54           | (v1_tops_1 @ X0 @ sk_A)
% 0.20/0.54           | ((k2_pre_topc @ sk_A @ X0) != (sk_B_1))))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.20/0.54  thf('89', plain,
% 0.20/0.54      (((((k2_pre_topc @ sk_A @ sk_B_1) != (sk_B_1))
% 0.20/0.54         | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['82', '88'])).
% 0.20/0.54  thf('90', plain,
% 0.20/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.54  thf('91', plain,
% 0.20/0.54      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.20/0.54         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.54  thf('92', plain,
% 0.20/0.54      ((((k3_subset_1 @ sk_B_1 @ sk_B_1)
% 0.20/0.54          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['90', '91'])).
% 0.20/0.54  thf('93', plain,
% 0.20/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.54  thf('94', plain,
% 0.20/0.54      ((((k3_subset_1 @ sk_B_1 @ sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_B_1)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['92', '93'])).
% 0.20/0.54  thf('95', plain,
% 0.20/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.54  thf('96', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.54          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X12) @ X11) @ X12)
% 0.20/0.54          | (v4_pre_topc @ X11 @ X12)
% 0.20/0.54          | ~ (l1_pre_topc @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.20/0.54  thf('97', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.20/0.54           | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54           | (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.54           | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['95', '96'])).
% 0.20/0.54  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('99', plain,
% 0.20/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.54  thf('100', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.20/0.54           | (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.54           | ~ (v3_pre_topc @ (k3_subset_1 @ sk_B_1 @ X0) @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.20/0.54  thf('101', plain,
% 0.20/0.54      (((~ (v3_pre_topc @ (k4_xboole_0 @ sk_B_1 @ sk_B_1) @ sk_A)
% 0.20/0.54         | (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.54         | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_B_1))))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['94', '100'])).
% 0.20/0.54  thf('102', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.54  thf('103', plain,
% 0.20/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.54  thf('104', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i]:
% 0.20/0.54         (~ (v1_tdlat_3 @ X18)
% 0.20/0.54          | (v3_pre_topc @ X19 @ X18)
% 0.20/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.54          | ~ (l1_pre_topc @ X18)
% 0.20/0.54          | ~ (v2_pre_topc @ X18))),
% 0.20/0.54      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.20/0.54  thf('105', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.20/0.54           | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54           | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54           | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.54           | ~ (v1_tdlat_3 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['103', '104'])).
% 0.20/0.54  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('108', plain, ((v1_tdlat_3 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('109', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.20/0.54           | (v3_pre_topc @ X0 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 0.20/0.54  thf('110', plain,
% 0.20/0.54      ((![X0 : $i]: (v3_pre_topc @ (k4_xboole_0 @ sk_B_1 @ X0) @ sk_A))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['102', '109'])).
% 0.20/0.54  thf('111', plain,
% 0.20/0.54      (((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_B_1)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['80', '81'])).
% 0.20/0.54  thf('112', plain,
% 0.20/0.54      (((v4_pre_topc @ sk_B_1 @ sk_A))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['101', '110', '111'])).
% 0.20/0.54  thf('113', plain,
% 0.20/0.54      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.20/0.54        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.54  thf('114', plain,
% 0.20/0.54      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['112', '113'])).
% 0.20/0.54  thf('115', plain,
% 0.20/0.54      (((((sk_B_1) != (sk_B_1)) | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['89', '114'])).
% 0.20/0.54  thf('116', plain,
% 0.20/0.54      (((v1_tops_1 @ sk_B_1 @ sk_A))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['115'])).
% 0.20/0.54  thf('117', plain, (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['3', '57'])).
% 0.20/0.54  thf('118', plain, ((v1_tops_1 @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['116', '117'])).
% 0.20/0.54  thf('119', plain, (((v2_struct_0 @ sk_A) | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['75', '118'])).
% 0.20/0.54  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('121', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('clc', [status(thm)], ['119', '120'])).
% 0.20/0.54  thf('122', plain, ($false), inference('demod', [status(thm)], ['60', '121'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
