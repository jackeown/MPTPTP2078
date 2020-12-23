%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gXZXbbe7wP

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:34 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 355 expanded)
%              Number of leaves         :   34 ( 115 expanded)
%              Depth                    :   15
%              Number of atoms          :  731 (4663 expanded)
%              Number of equality atoms :   31 (  73 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_subset_1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( v1_xboole_0 @ ( k3_subset_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( v1_subset_1 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( v1_xboole_0 @ ( k3_subset_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_tex_2])).

thf('2',plain,
    ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ~ ( v1_subset_1 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( v1_subset_1 @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('7',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['4','9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v1_tops_1 @ X13 @ X14 )
      | ( ( k2_pre_topc @ X14 @ X13 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v3_tdlat_3 @ X19 )
      | ~ ( v4_pre_topc @ X20 @ X19 )
      | ( v3_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('20',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_tops_1 @ X21 @ X22 )
      | ~ ( v3_tex_2 @ X21 @ X22 )
      | ~ ( v3_pre_topc @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('37',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('38',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('40',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v3_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('42',plain,(
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

thf('43',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_tdlat_3 @ X17 )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ( v4_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t23_tdlat_3])).

thf('44',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,(
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

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v4_pre_topc @ X11 @ X12 )
      | ( ( k2_pre_topc @ X12 @ X11 )
        = X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['40','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['4','9'])).

thf('58',plain,
    ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ sk_B_2 @ sk_B_2 ) )
   <= ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('59',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_subset_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('63',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = ( k3_subset_1 @ X4 @ ( k1_subset_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('64',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('65',plain,(
    ! [X4: $i] :
      ( X4
      = ( k3_subset_1 @ X4 @ ( k1_subset_1 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','66'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('69',plain,(
    ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['58','67','68'])).

thf('70',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('71',plain,(
    v4_pre_topc @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_tops_1 @ sk_B_2 @ sk_A ),
    inference(simpl_trail,[status(thm)],['35','71'])).

thf('73',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','72'])).

thf('74',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('75',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('76',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
   <= ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v4_pre_topc @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('78',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_2 )
    = sk_B_2 ),
    inference(simpl_trail,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_B_2 ),
    inference('sup+',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['10','79','80','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gXZXbbe7wP
% 0.14/0.37  % Computer   : n023.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 12:11:51 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.23/0.38  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 122 iterations in 0.055s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.55  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.35/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.35/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.55  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.35/0.55  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.35/0.55  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.35/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.55  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.35/0.55  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.35/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.35/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.35/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.35/0.55  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.35/0.55  thf(t61_tex_2, conjecture,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.35/0.55         ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.35/0.55                ( v3_tex_2 @ B @ A ) & 
% 0.35/0.55                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.35/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.55    (~( ![A:$i]:
% 0.35/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.35/0.55            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55          ( ![B:$i]:
% 0.35/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.35/0.55                   ( v3_tex_2 @ B @ A ) & 
% 0.35/0.55                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.35/0.55    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 0.35/0.55  thf('0', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(fc1_tex_2, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_subset_1 @ B @ A ) & 
% 0.35/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.35/0.55       ( ~( v1_xboole_0 @ ( k3_subset_1 @ A @ B ) ) ) ))).
% 0.35/0.55  thf('1', plain,
% 0.35/0.55      (![X15 : $i, X16 : $i]:
% 0.35/0.55         ((v1_xboole_0 @ X15)
% 0.35/0.55          | ~ (v1_subset_1 @ X16 @ X15)
% 0.35/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15))
% 0.35/0.55          | ~ (v1_xboole_0 @ (k3_subset_1 @ X15 @ X16)))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc1_tex_2])).
% 0.35/0.55  thf('2', plain,
% 0.35/0.55      ((~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.35/0.55        | ~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.55  thf('3', plain, ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('4', plain,
% 0.35/0.55      ((~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.35/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.35/0.55  thf('5', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(cc4_subset_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( v1_xboole_0 @ A ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.55           ( ~( v1_subset_1 @ B @ A ) ) ) ) ))).
% 0.35/0.55  thf('6', plain,
% 0.35/0.55      (![X6 : $i, X7 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.35/0.55          | ~ (v1_subset_1 @ X6 @ X7)
% 0.35/0.55          | ~ (v1_xboole_0 @ X7))),
% 0.35/0.55      inference('cnf', [status(esa)], [cc4_subset_1])).
% 0.35/0.55  thf('7', plain,
% 0.35/0.55      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | ~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.55  thf('8', plain, ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('9', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.35/0.55  thf('10', plain,
% 0.35/0.55      (~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))),
% 0.35/0.55      inference('clc', [status(thm)], ['4', '9'])).
% 0.35/0.55  thf('11', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(d2_tops_3, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( l1_pre_topc @ A ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55           ( ( v1_tops_1 @ B @ A ) <=>
% 0.35/0.55             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.35/0.55  thf('12', plain,
% 0.35/0.55      (![X13 : $i, X14 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.35/0.55          | ~ (v1_tops_1 @ X13 @ X14)
% 0.35/0.55          | ((k2_pre_topc @ X14 @ X13) = (u1_struct_0 @ X14))
% 0.35/0.55          | ~ (l1_pre_topc @ X14))),
% 0.35/0.55      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.35/0.55  thf('13', plain,
% 0.35/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.55        | ((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.35/0.55        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.55  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('15', plain,
% 0.35/0.55      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.35/0.55        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.35/0.55  thf('16', plain,
% 0.35/0.55      (((v3_pre_topc @ sk_B_2 @ sk_A) | (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('17', plain,
% 0.35/0.55      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.35/0.55      inference('split', [status(esa)], ['16'])).
% 0.35/0.55  thf('18', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(t24_tdlat_3, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ( v3_tdlat_3 @ A ) <=>
% 0.35/0.55         ( ![B:$i]:
% 0.35/0.55           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.35/0.55  thf('19', plain,
% 0.35/0.55      (![X19 : $i, X20 : $i]:
% 0.35/0.55         (~ (v3_tdlat_3 @ X19)
% 0.35/0.55          | ~ (v4_pre_topc @ X20 @ X19)
% 0.35/0.55          | (v3_pre_topc @ X20 @ X19)
% 0.35/0.55          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.35/0.55          | ~ (l1_pre_topc @ X19)
% 0.35/0.55          | ~ (v2_pre_topc @ X19))),
% 0.35/0.55      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.35/0.55  thf('20', plain,
% 0.35/0.55      ((~ (v2_pre_topc @ sk_A)
% 0.35/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55        | (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.35/0.55        | ~ (v4_pre_topc @ sk_B_2 @ sk_A)
% 0.35/0.55        | ~ (v3_tdlat_3 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.35/0.55  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('23', plain, ((v3_tdlat_3 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('24', plain,
% 0.35/0.55      (((v3_pre_topc @ sk_B_2 @ sk_A) | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.35/0.55  thf('25', plain,
% 0.35/0.55      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['17', '24'])).
% 0.35/0.55  thf('26', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(t47_tex_2, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.35/0.55             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.35/0.55  thf('27', plain,
% 0.35/0.55      (![X21 : $i, X22 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.35/0.55          | (v1_tops_1 @ X21 @ X22)
% 0.35/0.55          | ~ (v3_tex_2 @ X21 @ X22)
% 0.35/0.55          | ~ (v3_pre_topc @ X21 @ X22)
% 0.35/0.55          | ~ (l1_pre_topc @ X22)
% 0.35/0.55          | ~ (v2_pre_topc @ X22)
% 0.35/0.55          | (v2_struct_0 @ X22))),
% 0.35/0.55      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.35/0.55  thf('28', plain,
% 0.35/0.55      (((v2_struct_0 @ sk_A)
% 0.35/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.35/0.55        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 0.35/0.55        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.35/0.55  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('31', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('32', plain,
% 0.35/0.55      (((v2_struct_0 @ sk_A)
% 0.35/0.55        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.35/0.55        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.35/0.55  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('34', plain,
% 0.35/0.55      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.35/0.55      inference('clc', [status(thm)], ['32', '33'])).
% 0.35/0.55  thf('35', plain,
% 0.35/0.55      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['25', '34'])).
% 0.35/0.55  thf('36', plain,
% 0.35/0.55      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.35/0.55      inference('split', [status(esa)], ['16'])).
% 0.35/0.55  thf('37', plain,
% 0.35/0.55      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.35/0.55      inference('clc', [status(thm)], ['32', '33'])).
% 0.35/0.55  thf('38', plain,
% 0.35/0.55      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.35/0.55  thf('39', plain,
% 0.35/0.55      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.35/0.55        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.35/0.55  thf('40', plain,
% 0.35/0.55      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A)))
% 0.35/0.55         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.35/0.55  thf('41', plain,
% 0.35/0.55      (((v3_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.35/0.55      inference('split', [status(esa)], ['16'])).
% 0.35/0.55  thf('42', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(t23_tdlat_3, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ( v3_tdlat_3 @ A ) <=>
% 0.35/0.55         ( ![B:$i]:
% 0.35/0.55           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55             ( ( v3_pre_topc @ B @ A ) => ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.35/0.55  thf('43', plain,
% 0.35/0.55      (![X17 : $i, X18 : $i]:
% 0.35/0.55         (~ (v3_tdlat_3 @ X17)
% 0.35/0.55          | ~ (v3_pre_topc @ X18 @ X17)
% 0.35/0.55          | (v4_pre_topc @ X18 @ X17)
% 0.35/0.55          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.55          | ~ (l1_pre_topc @ X17)
% 0.35/0.55          | ~ (v2_pre_topc @ X17))),
% 0.35/0.55      inference('cnf', [status(esa)], [t23_tdlat_3])).
% 0.35/0.55  thf('44', plain,
% 0.35/0.55      ((~ (v2_pre_topc @ sk_A)
% 0.35/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55        | (v4_pre_topc @ sk_B_2 @ sk_A)
% 0.35/0.55        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 0.35/0.55        | ~ (v3_tdlat_3 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.35/0.55  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('47', plain, ((v3_tdlat_3 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('48', plain,
% 0.35/0.55      (((v4_pre_topc @ sk_B_2 @ sk_A) | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.35/0.55  thf('49', plain,
% 0.35/0.55      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['41', '48'])).
% 0.35/0.55  thf('50', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(t52_pre_topc, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( l1_pre_topc @ A ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.35/0.55             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.35/0.55               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.35/0.55  thf('51', plain,
% 0.35/0.55      (![X11 : $i, X12 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.35/0.55          | ~ (v4_pre_topc @ X11 @ X12)
% 0.35/0.55          | ((k2_pre_topc @ X12 @ X11) = (X11))
% 0.35/0.55          | ~ (l1_pre_topc @ X12))),
% 0.35/0.55      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.35/0.55  thf('52', plain,
% 0.35/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.55        | ((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.35/0.55        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.35/0.55  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('54', plain,
% 0.35/0.55      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.35/0.55        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['52', '53'])).
% 0.35/0.55  thf('55', plain,
% 0.35/0.55      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))
% 0.35/0.55         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['49', '54'])).
% 0.35/0.55  thf('56', plain,
% 0.35/0.55      ((((u1_struct_0 @ sk_A) = (sk_B_2))) <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.35/0.55      inference('sup+', [status(thm)], ['40', '55'])).
% 0.35/0.55  thf('57', plain,
% 0.35/0.55      (~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))),
% 0.35/0.55      inference('clc', [status(thm)], ['4', '9'])).
% 0.35/0.55  thf('58', plain,
% 0.35/0.55      ((~ (v1_xboole_0 @ (k3_subset_1 @ sk_B_2 @ sk_B_2)))
% 0.35/0.55         <= (((v3_pre_topc @ sk_B_2 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['56', '57'])).
% 0.35/0.55  thf(t4_subset_1, axiom,
% 0.35/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.35/0.55  thf('59', plain,
% 0.35/0.55      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.35/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.35/0.55  thf(involutiveness_k3_subset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.55       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.35/0.55  thf('60', plain,
% 0.35/0.55      (![X2 : $i, X3 : $i]:
% 0.35/0.55         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 0.35/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.35/0.55      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.35/0.55  thf('61', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['59', '60'])).
% 0.35/0.55  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.35/0.55  thf('62', plain, (![X0 : $i]: ((k1_subset_1 @ X0) = (k1_xboole_0))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.35/0.55  thf(t22_subset_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.35/0.55  thf('63', plain,
% 0.35/0.55      (![X4 : $i]:
% 0.35/0.55         ((k2_subset_1 @ X4) = (k3_subset_1 @ X4 @ (k1_subset_1 @ X4)))),
% 0.35/0.55      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.35/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.35/0.55  thf('64', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.35/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.35/0.55  thf('65', plain,
% 0.35/0.55      (![X4 : $i]: ((X4) = (k3_subset_1 @ X4 @ (k1_subset_1 @ X4)))),
% 0.35/0.55      inference('demod', [status(thm)], ['63', '64'])).
% 0.35/0.55  thf('66', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.35/0.55      inference('sup+', [status(thm)], ['62', '65'])).
% 0.35/0.55  thf('67', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.35/0.55      inference('demod', [status(thm)], ['61', '66'])).
% 0.35/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.35/0.55  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.35/0.55  thf('69', plain, (~ ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['58', '67', '68'])).
% 0.35/0.55  thf('70', plain,
% 0.35/0.55      (((v4_pre_topc @ sk_B_2 @ sk_A)) | ((v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.35/0.55      inference('split', [status(esa)], ['16'])).
% 0.35/0.55  thf('71', plain, (((v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.35/0.55      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 0.35/0.55  thf('72', plain, ((v1_tops_1 @ sk_B_2 @ sk_A)),
% 0.35/0.55      inference('simpl_trail', [status(thm)], ['35', '71'])).
% 0.35/0.55  thf('73', plain, (((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['15', '72'])).
% 0.35/0.55  thf('74', plain,
% 0.35/0.55      (((v4_pre_topc @ sk_B_2 @ sk_A)) <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.35/0.55      inference('split', [status(esa)], ['16'])).
% 0.35/0.55  thf('75', plain,
% 0.35/0.55      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 0.35/0.55        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['52', '53'])).
% 0.35/0.55  thf('76', plain,
% 0.35/0.55      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))
% 0.35/0.55         <= (((v4_pre_topc @ sk_B_2 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['74', '75'])).
% 0.35/0.55  thf('77', plain, (((v4_pre_topc @ sk_B_2 @ sk_A))),
% 0.35/0.55      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 0.35/0.55  thf('78', plain, (((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))),
% 0.35/0.55      inference('simpl_trail', [status(thm)], ['76', '77'])).
% 0.35/0.55  thf('79', plain, (((u1_struct_0 @ sk_A) = (sk_B_2))),
% 0.35/0.55      inference('sup+', [status(thm)], ['73', '78'])).
% 0.35/0.55  thf('80', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.35/0.55      inference('demod', [status(thm)], ['61', '66'])).
% 0.35/0.55  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.35/0.55  thf('82', plain, ($false),
% 0.35/0.55      inference('demod', [status(thm)], ['10', '79', '80', '81'])).
% 0.35/0.55  
% 0.35/0.55  % SZS output end Refutation
% 0.35/0.55  
% 0.39/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
