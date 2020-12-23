%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hMSr8CLqNE

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:34 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 423 expanded)
%              Number of leaves         :   35 ( 135 expanded)
%              Depth                    :   16
%              Number of atoms          :  914 (5681 expanded)
%              Number of equality atoms :   34 (  80 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

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
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_subset_1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( v1_xboole_0 @ ( k3_subset_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( v1_subset_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( v1_xboole_0 @ ( k3_subset_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_tex_2])).

thf('2',plain,
    ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ~ ( v1_subset_1 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( v1_subset_1 @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('7',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['4','9'])).

thf('11',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v4_pre_topc @ X13 @ X14 )
      | ( ( k2_pre_topc @ X14 @ X13 )
        = X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v1_tops_1 @ X23 @ X24 )
      | ~ ( v3_tex_2 @ X23 @ X24 )
      | ~ ( v3_pre_topc @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v1_tops_1 @ X17 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('39',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 ) @ X16 )
      | ( v4_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('45',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','45'])).

thf('47',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('49',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v3_tdlat_3 @ X21 )
      | ~ ( v4_pre_topc @ X22 @ X21 )
      | ( v3_pre_topc @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('50',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 ) @ X16 )
      | ( v4_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('63',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','63'])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['4','9'])).

thf('66',plain,
    ( ~ ( v1_xboole_0 @ ( k3_subset_1 @ sk_B_1 @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('67',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('68',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k1_subset_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('71',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = ( k3_subset_1 @ X6 @ ( k1_subset_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('72',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('73',plain,(
    ! [X6: $i] :
      ( X6
      = ( k3_subset_1 @ X6 @ ( k1_subset_1 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','74'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('77',plain,(
    ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['66','75','76'])).

thf('78',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('79',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['18','79'])).

thf('81',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('82',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v3_tdlat_3 @ X21 )
      | ~ ( v4_pre_topc @ X22 @ X21 )
      | ( v3_pre_topc @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('84',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','88'])).

thf('90',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('91',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('93',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['77','78'])).

thf('95',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['93','94'])).

thf('96',plain,
    ( sk_B_1
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['80','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','74'])).

thf('98',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['10','96','97','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hMSr8CLqNE
% 0.14/0.38  % Computer   : n015.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 12:02:08 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.23/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.57  % Solved by: fo/fo7.sh
% 0.23/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.57  % done 154 iterations in 0.074s
% 0.23/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.57  % SZS output start Refutation
% 0.23/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.57  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.23/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.57  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.23/0.57  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.23/0.57  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.23/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.57  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.23/0.57  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.23/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.23/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.57  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.23/0.57  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.23/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.57  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.23/0.57  thf(t61_tex_2, conjecture,
% 0.23/0.57    (![A:$i]:
% 0.23/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.23/0.57         ( l1_pre_topc @ A ) ) =>
% 0.23/0.57       ( ![B:$i]:
% 0.23/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.57           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.23/0.57                ( v3_tex_2 @ B @ A ) & 
% 0.23/0.57                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.23/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.57    (~( ![A:$i]:
% 0.23/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.23/0.57            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.57          ( ![B:$i]:
% 0.23/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.57              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 0.23/0.57                   ( v3_tex_2 @ B @ A ) & 
% 0.23/0.57                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.23/0.57    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 0.23/0.57  thf('0', plain,
% 0.23/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf(fc1_tex_2, axiom,
% 0.23/0.57    (![A:$i,B:$i]:
% 0.23/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_subset_1 @ B @ A ) & 
% 0.23/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.57       ( ~( v1_xboole_0 @ ( k3_subset_1 @ A @ B ) ) ) ))).
% 0.23/0.57  thf('1', plain,
% 0.23/0.57      (![X19 : $i, X20 : $i]:
% 0.23/0.57         ((v1_xboole_0 @ X19)
% 0.23/0.57          | ~ (v1_subset_1 @ X20 @ X19)
% 0.23/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19))
% 0.23/0.57          | ~ (v1_xboole_0 @ (k3_subset_1 @ X19 @ X20)))),
% 0.23/0.57      inference('cnf', [status(esa)], [fc1_tex_2])).
% 0.23/0.57  thf('2', plain,
% 0.23/0.57      ((~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.23/0.57        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.23/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.57  thf('3', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('4', plain,
% 0.23/0.57      ((~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.23/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.57      inference('demod', [status(thm)], ['2', '3'])).
% 0.23/0.57  thf('5', plain,
% 0.23/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf(cc4_subset_1, axiom,
% 0.23/0.57    (![A:$i]:
% 0.23/0.57     ( ( v1_xboole_0 @ A ) =>
% 0.23/0.57       ( ![B:$i]:
% 0.23/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.57           ( ~( v1_subset_1 @ B @ A ) ) ) ) ))).
% 0.23/0.57  thf('6', plain,
% 0.23/0.57      (![X8 : $i, X9 : $i]:
% 0.23/0.57         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.23/0.57          | ~ (v1_subset_1 @ X8 @ X9)
% 0.23/0.57          | ~ (v1_xboole_0 @ X9))),
% 0.23/0.57      inference('cnf', [status(esa)], [cc4_subset_1])).
% 0.23/0.57  thf('7', plain,
% 0.23/0.57      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.57        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.57  thf('8', plain, ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('9', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.23/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.23/0.57  thf('10', plain,
% 0.23/0.57      (~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.23/0.57      inference('clc', [status(thm)], ['4', '9'])).
% 0.23/0.57  thf('11', plain,
% 0.23/0.57      (((v3_pre_topc @ sk_B_1 @ sk_A) | (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('12', plain,
% 0.23/0.57      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.23/0.57      inference('split', [status(esa)], ['11'])).
% 0.23/0.57  thf('13', plain,
% 0.23/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf(t52_pre_topc, axiom,
% 0.23/0.57    (![A:$i]:
% 0.23/0.57     ( ( l1_pre_topc @ A ) =>
% 0.23/0.57       ( ![B:$i]:
% 0.23/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.57           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.23/0.57             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.23/0.57               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.23/0.57  thf('14', plain,
% 0.23/0.57      (![X13 : $i, X14 : $i]:
% 0.23/0.57         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.23/0.57          | ~ (v4_pre_topc @ X13 @ X14)
% 0.23/0.57          | ((k2_pre_topc @ X14 @ X13) = (X13))
% 0.23/0.57          | ~ (l1_pre_topc @ X14))),
% 0.23/0.57      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.23/0.57  thf('15', plain,
% 0.23/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.57        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.23/0.57        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.23/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.23/0.57  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('17', plain,
% 0.23/0.57      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.23/0.57        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.23/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.23/0.57  thf('18', plain,
% 0.23/0.57      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.23/0.57         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.23/0.57      inference('sup-', [status(thm)], ['12', '17'])).
% 0.23/0.57  thf('19', plain,
% 0.23/0.57      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.23/0.57      inference('split', [status(esa)], ['11'])).
% 0.23/0.57  thf('20', plain,
% 0.23/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf(t47_tex_2, axiom,
% 0.23/0.57    (![A:$i]:
% 0.23/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.57       ( ![B:$i]:
% 0.23/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.57           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.23/0.57             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.23/0.57  thf('21', plain,
% 0.23/0.57      (![X23 : $i, X24 : $i]:
% 0.23/0.57         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.23/0.57          | (v1_tops_1 @ X23 @ X24)
% 0.23/0.57          | ~ (v3_tex_2 @ X23 @ X24)
% 0.23/0.57          | ~ (v3_pre_topc @ X23 @ X24)
% 0.23/0.57          | ~ (l1_pre_topc @ X24)
% 0.23/0.57          | ~ (v2_pre_topc @ X24)
% 0.23/0.57          | (v2_struct_0 @ X24))),
% 0.23/0.57      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.23/0.57  thf('22', plain,
% 0.23/0.57      (((v2_struct_0 @ sk_A)
% 0.23/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.23/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.57        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.23/0.57        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.23/0.57        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.23/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.23/0.57  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('25', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('26', plain,
% 0.23/0.57      (((v2_struct_0 @ sk_A)
% 0.23/0.57        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.23/0.57        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.23/0.57      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.23/0.57  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('28', plain,
% 0.23/0.57      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.23/0.57      inference('clc', [status(thm)], ['26', '27'])).
% 0.23/0.57  thf('29', plain,
% 0.23/0.57      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.23/0.57      inference('sup-', [status(thm)], ['19', '28'])).
% 0.23/0.57  thf('30', plain,
% 0.23/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf(d2_tops_3, axiom,
% 0.23/0.57    (![A:$i]:
% 0.23/0.57     ( ( l1_pre_topc @ A ) =>
% 0.23/0.57       ( ![B:$i]:
% 0.23/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.57           ( ( v1_tops_1 @ B @ A ) <=>
% 0.23/0.57             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.23/0.57  thf('31', plain,
% 0.23/0.57      (![X17 : $i, X18 : $i]:
% 0.23/0.57         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.23/0.57          | ~ (v1_tops_1 @ X17 @ X18)
% 0.23/0.57          | ((k2_pre_topc @ X18 @ X17) = (u1_struct_0 @ X18))
% 0.23/0.57          | ~ (l1_pre_topc @ X18))),
% 0.23/0.57      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.23/0.57  thf('32', plain,
% 0.23/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.57        | ((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.23/0.57        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.23/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.23/0.57  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('34', plain,
% 0.23/0.57      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.23/0.57        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.23/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.23/0.57  thf('35', plain,
% 0.23/0.57      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.23/0.57         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.23/0.57      inference('sup-', [status(thm)], ['29', '34'])).
% 0.23/0.57  thf('36', plain,
% 0.23/0.57      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.23/0.57      inference('split', [status(esa)], ['11'])).
% 0.23/0.57  thf('37', plain,
% 0.23/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf(dt_k3_subset_1, axiom,
% 0.23/0.57    (![A:$i,B:$i]:
% 0.23/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.57       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.57  thf('38', plain,
% 0.23/0.57      (![X2 : $i, X3 : $i]:
% 0.23/0.57         ((m1_subset_1 @ (k3_subset_1 @ X2 @ X3) @ (k1_zfmisc_1 @ X2))
% 0.23/0.57          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.23/0.57      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.23/0.57  thf('39', plain,
% 0.23/0.57      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.23/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.23/0.57  thf(t29_tops_1, axiom,
% 0.23/0.57    (![A:$i]:
% 0.23/0.57     ( ( l1_pre_topc @ A ) =>
% 0.23/0.57       ( ![B:$i]:
% 0.23/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.57           ( ( v4_pre_topc @ B @ A ) <=>
% 0.23/0.57             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.23/0.57  thf('40', plain,
% 0.23/0.57      (![X15 : $i, X16 : $i]:
% 0.23/0.57         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.23/0.57          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X16) @ X15) @ X16)
% 0.23/0.57          | (v4_pre_topc @ X15 @ X16)
% 0.23/0.57          | ~ (l1_pre_topc @ X16))),
% 0.23/0.57      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.23/0.57  thf('41', plain,
% 0.23/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.57        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.23/0.57        | ~ (v3_pre_topc @ 
% 0.23/0.57             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.57              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.23/0.57             sk_A))),
% 0.23/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.23/0.57  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('43', plain,
% 0.23/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf(involutiveness_k3_subset_1, axiom,
% 0.23/0.57    (![A:$i,B:$i]:
% 0.23/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.57       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.23/0.57  thf('44', plain,
% 0.23/0.57      (![X4 : $i, X5 : $i]:
% 0.23/0.57         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.23/0.57          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.23/0.57      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.23/0.57  thf('45', plain,
% 0.23/0.57      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.57         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 0.23/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.23/0.57  thf('46', plain,
% 0.23/0.57      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.23/0.57        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.23/0.57      inference('demod', [status(thm)], ['41', '42', '45'])).
% 0.23/0.57  thf('47', plain,
% 0.23/0.57      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))
% 0.23/0.57         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.23/0.57      inference('sup-', [status(thm)], ['36', '46'])).
% 0.23/0.57  thf('48', plain,
% 0.23/0.57      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.23/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.23/0.57  thf(t24_tdlat_3, axiom,
% 0.23/0.57    (![A:$i]:
% 0.23/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.57       ( ( v3_tdlat_3 @ A ) <=>
% 0.23/0.57         ( ![B:$i]:
% 0.23/0.57           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.57             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.23/0.57  thf('49', plain,
% 0.23/0.57      (![X21 : $i, X22 : $i]:
% 0.23/0.57         (~ (v3_tdlat_3 @ X21)
% 0.23/0.57          | ~ (v4_pre_topc @ X22 @ X21)
% 0.23/0.57          | (v3_pre_topc @ X22 @ X21)
% 0.23/0.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.23/0.57          | ~ (l1_pre_topc @ X21)
% 0.23/0.57          | ~ (v2_pre_topc @ X21))),
% 0.23/0.57      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.23/0.57  thf('50', plain,
% 0.23/0.57      ((~ (v2_pre_topc @ sk_A)
% 0.23/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.57        | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.23/0.57        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.23/0.57        | ~ (v3_tdlat_3 @ sk_A))),
% 0.23/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.23/0.57  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('53', plain, ((v3_tdlat_3 @ sk_A)),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('54', plain,
% 0.23/0.57      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.23/0.57        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.23/0.57      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.23/0.57  thf('55', plain,
% 0.23/0.57      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))
% 0.23/0.57         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.23/0.57      inference('sup-', [status(thm)], ['47', '54'])).
% 0.23/0.57  thf('56', plain,
% 0.23/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('57', plain,
% 0.23/0.57      (![X15 : $i, X16 : $i]:
% 0.23/0.57         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.23/0.57          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X16) @ X15) @ X16)
% 0.23/0.57          | (v4_pre_topc @ X15 @ X16)
% 0.23/0.57          | ~ (l1_pre_topc @ X16))),
% 0.23/0.57      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.23/0.57  thf('58', plain,
% 0.23/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.57        | (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.23/0.57        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.23/0.57      inference('sup-', [status(thm)], ['56', '57'])).
% 0.23/0.57  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('60', plain,
% 0.23/0.57      (((v4_pre_topc @ sk_B_1 @ sk_A)
% 0.23/0.57        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.23/0.57      inference('demod', [status(thm)], ['58', '59'])).
% 0.23/0.57  thf('61', plain,
% 0.23/0.57      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.23/0.57      inference('sup-', [status(thm)], ['55', '60'])).
% 0.23/0.57  thf('62', plain,
% 0.23/0.57      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.23/0.57        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.23/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.23/0.57  thf('63', plain,
% 0.23/0.57      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.23/0.57         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.23/0.57      inference('sup-', [status(thm)], ['61', '62'])).
% 0.23/0.57  thf('64', plain,
% 0.23/0.57      ((((u1_struct_0 @ sk_A) = (sk_B_1))) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.23/0.57      inference('sup+', [status(thm)], ['35', '63'])).
% 0.23/0.57  thf('65', plain,
% 0.23/0.57      (~ (v1_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.23/0.57      inference('clc', [status(thm)], ['4', '9'])).
% 0.23/0.57  thf('66', plain,
% 0.23/0.57      ((~ (v1_xboole_0 @ (k3_subset_1 @ sk_B_1 @ sk_B_1)))
% 0.23/0.57         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.23/0.57      inference('sup-', [status(thm)], ['64', '65'])).
% 0.23/0.57  thf(t4_subset_1, axiom,
% 0.23/0.57    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.23/0.57  thf('67', plain,
% 0.23/0.57      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.23/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.23/0.57  thf('68', plain,
% 0.23/0.57      (![X4 : $i, X5 : $i]:
% 0.23/0.57         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.23/0.57          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.23/0.57      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.23/0.57  thf('69', plain,
% 0.23/0.57      (![X0 : $i]:
% 0.23/0.57         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.23/0.57      inference('sup-', [status(thm)], ['67', '68'])).
% 0.23/0.57  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.23/0.57  thf('70', plain, (![X0 : $i]: ((k1_subset_1 @ X0) = (k1_xboole_0))),
% 0.23/0.57      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.23/0.57  thf(t22_subset_1, axiom,
% 0.23/0.57    (![A:$i]:
% 0.23/0.57     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.23/0.57  thf('71', plain,
% 0.23/0.57      (![X6 : $i]:
% 0.23/0.57         ((k2_subset_1 @ X6) = (k3_subset_1 @ X6 @ (k1_subset_1 @ X6)))),
% 0.23/0.57      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.23/0.57  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.23/0.57  thf('72', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.23/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.23/0.57  thf('73', plain,
% 0.23/0.57      (![X6 : $i]: ((X6) = (k3_subset_1 @ X6 @ (k1_subset_1 @ X6)))),
% 0.23/0.57      inference('demod', [status(thm)], ['71', '72'])).
% 0.23/0.57  thf('74', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.23/0.57      inference('sup+', [status(thm)], ['70', '73'])).
% 0.23/0.57  thf('75', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.23/0.57      inference('demod', [status(thm)], ['69', '74'])).
% 0.23/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.23/0.57  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.23/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.23/0.57  thf('77', plain, (~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.23/0.57      inference('demod', [status(thm)], ['66', '75', '76'])).
% 0.23/0.57  thf('78', plain,
% 0.23/0.57      (((v4_pre_topc @ sk_B_1 @ sk_A)) | ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.23/0.57      inference('split', [status(esa)], ['11'])).
% 0.23/0.57  thf('79', plain, (((v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.23/0.57      inference('sat_resolution*', [status(thm)], ['77', '78'])).
% 0.23/0.57  thf('80', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.23/0.57      inference('simpl_trail', [status(thm)], ['18', '79'])).
% 0.23/0.57  thf('81', plain,
% 0.23/0.57      (((v4_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.23/0.57      inference('split', [status(esa)], ['11'])).
% 0.23/0.57  thf('82', plain,
% 0.23/0.57      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('83', plain,
% 0.23/0.57      (![X21 : $i, X22 : $i]:
% 0.23/0.57         (~ (v3_tdlat_3 @ X21)
% 0.23/0.57          | ~ (v4_pre_topc @ X22 @ X21)
% 0.23/0.57          | (v3_pre_topc @ X22 @ X21)
% 0.23/0.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.23/0.57          | ~ (l1_pre_topc @ X21)
% 0.23/0.57          | ~ (v2_pre_topc @ X21))),
% 0.23/0.57      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.23/0.57  thf('84', plain,
% 0.23/0.57      ((~ (v2_pre_topc @ sk_A)
% 0.23/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.57        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.23/0.57        | ~ (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.23/0.57        | ~ (v3_tdlat_3 @ sk_A))),
% 0.23/0.57      inference('sup-', [status(thm)], ['82', '83'])).
% 0.23/0.57  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('87', plain, ((v3_tdlat_3 @ sk_A)),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('88', plain,
% 0.23/0.57      (((v3_pre_topc @ sk_B_1 @ sk_A) | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.23/0.57      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 0.23/0.57  thf('89', plain,
% 0.23/0.57      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.23/0.57      inference('sup-', [status(thm)], ['81', '88'])).
% 0.23/0.57  thf('90', plain,
% 0.23/0.57      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.23/0.57      inference('clc', [status(thm)], ['26', '27'])).
% 0.23/0.57  thf('91', plain,
% 0.23/0.57      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.23/0.57      inference('sup-', [status(thm)], ['89', '90'])).
% 0.23/0.57  thf('92', plain,
% 0.23/0.57      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.23/0.57        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.23/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.23/0.57  thf('93', plain,
% 0.23/0.57      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.23/0.57         <= (((v4_pre_topc @ sk_B_1 @ sk_A)))),
% 0.23/0.57      inference('sup-', [status(thm)], ['91', '92'])).
% 0.23/0.57  thf('94', plain, (((v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.23/0.57      inference('sat_resolution*', [status(thm)], ['77', '78'])).
% 0.23/0.57  thf('95', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.23/0.57      inference('simpl_trail', [status(thm)], ['93', '94'])).
% 0.23/0.57  thf('96', plain, (((sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.23/0.57      inference('sup+', [status(thm)], ['80', '95'])).
% 0.23/0.57  thf('97', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.23/0.57      inference('demod', [status(thm)], ['69', '74'])).
% 0.23/0.57  thf('98', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.23/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.23/0.57  thf('99', plain, ($false),
% 0.23/0.57      inference('demod', [status(thm)], ['10', '96', '97', '98'])).
% 0.23/0.57  
% 0.23/0.57  % SZS output end Refutation
% 0.23/0.57  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
