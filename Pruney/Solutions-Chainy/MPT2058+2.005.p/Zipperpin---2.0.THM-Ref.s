%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xa6fTCgdnm

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:48 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  294 ( 950 expanded)
%              Number of leaves         :   44 ( 308 expanded)
%              Depth                    :   40
%              Number of atoms          : 3858 (17353 expanded)
%              Number of equality atoms :   49 ( 233 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(t17_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r3_waybel_9 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C )
              <=> ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
              & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
              & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r3_waybel_9 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C )
                <=> ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_yellow19])).

thf('0',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( r2_hidden @ X13 @ ( k1_connsp_2 @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_C @ ( k1_connsp_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( k1_connsp_2 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ sk_C @ ( k1_connsp_2 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('10',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('11',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('17',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('19',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(fc5_yellow19,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ~ ( v1_xboole_0 @ C )
        & ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) )
        & ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) )
        & ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) )
     => ( ~ ( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) )
        & ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A )
        & ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ) )).

thf('25',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v1_xboole_0 @ X22 )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( v1_subset_1 @ X24 @ ( u1_struct_0 @ ( k3_yellow_1 @ X22 ) ) )
      | ~ ( v2_waybel_0 @ X24 @ ( k3_yellow_1 @ X22 ) )
      | ~ ( v13_waybel_0 @ X24 @ ( k3_yellow_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X22 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X23 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('26',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('27',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('28',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('29',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('30',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v1_xboole_0 @ X22 )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( v1_subset_1 @ X24 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) )
      | ~ ( v2_waybel_0 @ X24 @ ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) )
      | ~ ( v13_waybel_0 @ X24 @ ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X23 @ X22 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('33',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('36',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('42',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('43',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('45',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('54',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['31','40','49','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','59'])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('65',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(fc4_yellow19,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ~ ( v1_xboole_0 @ C )
        & ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) )
        & ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) )
     => ( ~ ( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) )
        & ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) )
        & ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) )
        & ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ) )).

thf('67',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_xboole_0 @ X19 )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( v2_waybel_0 @ X21 @ ( k3_yellow_1 @ X19 ) )
      | ~ ( v13_waybel_0 @ X21 @ ( k3_yellow_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X19 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X20 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('68',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('69',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('70',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('71',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_xboole_0 @ X19 )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( v2_waybel_0 @ X21 @ ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) )
      | ~ ( v13_waybel_0 @ X21 @ ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X20 @ X19 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('74',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','75'])).

thf('77',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('81',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(dt_k3_yellow19,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ~ ( v1_xboole_0 @ C )
        & ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) )
        & ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) )
     => ( ~ ( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) )
        & ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A )
        & ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ) )).

thf('83',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_xboole_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( v2_waybel_0 @ X18 @ ( k3_yellow_1 @ X16 ) )
      | ~ ( v13_waybel_0 @ X18 @ ( k3_yellow_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X16 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X17 @ X16 @ X18 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('84',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('85',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('86',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('87',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_xboole_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( v2_waybel_0 @ X18 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) )
      | ~ ( v13_waybel_0 @ X18 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X17 @ X16 @ X18 ) @ X17 ) ) ),
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('90',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['81','91'])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('97',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('98',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['98'])).

thf('100',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['97','99'])).

thf('101',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['96','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r3_waybel_9 @ A @ B @ C )
              <=> ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) )).

thf('105',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v7_waybel_0 @ X25 )
      | ~ ( l1_waybel_0 @ X25 @ X26 )
      | ~ ( r3_waybel_9 @ X26 @ X25 @ X27 )
      | ( r1_waybel_7 @ X26 @ ( k2_yellow19 @ X26 @ X25 ) @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['103','109'])).

thf('111',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['95','110'])).

thf('112',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['79','112'])).

thf('114',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('115',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('116',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('117',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t15_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
         => ( B
            = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('118',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v1_subset_1 @ X28 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X29 ) ) ) )
      | ~ ( v2_waybel_0 @ X28 @ ( k3_yellow_1 @ ( k2_struct_0 @ X29 ) ) )
      | ~ ( v13_waybel_0 @ X28 @ ( k3_yellow_1 @ ( k2_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X29 ) ) ) ) )
      | ( X28
        = ( k2_yellow19 @ X29 @ ( k3_yellow19 @ X29 @ ( k2_struct_0 @ X29 ) @ X28 ) ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('119',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('120',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('121',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('122',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('123',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v1_subset_1 @ X28 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X28 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) )
      | ~ ( v13_waybel_0 @ X28 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) ) ) )
      | ( X28
        = ( k2_yellow19 @ X29 @ ( k3_yellow19 @ X29 @ ( k2_struct_0 @ X29 ) @ X28 ) ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(demod,[status(thm)],['118','119','120','121','122'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['117','123'])).

thf('125',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('126',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('127',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['124','125','126','127'])).

thf('129',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['116','128'])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['115','135'])).

thf('137',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['114','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['113','139'])).

thf('141',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['63','141'])).

thf('143',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('145',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('146',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_xboole_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( v2_waybel_0 @ X18 @ ( k3_yellow_1 @ X16 ) )
      | ~ ( v13_waybel_0 @ X18 @ ( k3_yellow_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X16 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X17 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('147',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('148',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('149',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('150',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_xboole_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( v2_waybel_0 @ X18 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) )
      | ~ ( v13_waybel_0 @ X18 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X17 @ X16 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['145','150'])).

thf('152',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('153',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['144','154'])).

thf('156',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['143','155'])).

thf('157',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['10','157'])).

thf('159',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('162',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('168',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('169',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['172','173'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('175',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_A @ sk_C ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['166','176'])).

thf('178',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['9','177'])).

thf('179',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['98'])).

thf('180',plain,(
    r2_hidden @ sk_C @ ( k1_connsp_2 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('181',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('182',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('183',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('184',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['98'])).

thf('185',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('186',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('187',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('188',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('189',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('190',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('191',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('192',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('193',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v7_waybel_0 @ X25 )
      | ~ ( l1_waybel_0 @ X25 @ X26 )
      | ~ ( r1_waybel_7 @ X26 @ ( k2_yellow19 @ X26 @ X25 ) @ X27 )
      | ( r3_waybel_9 @ X26 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['191','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['190','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['189','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['188','202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['187','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['186','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['185','208'])).

thf('210',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['209','210'])).

thf('212',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['184','211'])).

thf('213',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('216',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('218',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('219',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('220',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('221',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_xboole_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( v2_waybel_0 @ X18 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) )
      | ~ ( v13_waybel_0 @ X18 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X17 @ X16 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('224',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['222','223','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['219','225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['218','226'])).

thf('228',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['217','229'])).

thf('231',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['216','230'])).

thf('232',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['231'])).

thf('233',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['183','232'])).

thf('234',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['182','235'])).

thf('237',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['181','237'])).

thf('239',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['238','239'])).

thf('241',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['240','241'])).

thf('243',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('246',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_A @ sk_C ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['180','246'])).

thf('248',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','178','179','247'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xa6fTCgdnm
% 0.13/0.37  % Computer   : n023.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 20:29:51 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.40/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.63  % Solved by: fo/fo7.sh
% 0.40/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.63  % done 212 iterations in 0.135s
% 0.40/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.63  % SZS output start Refutation
% 0.40/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.63  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.40/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.63  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 0.40/0.63  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.40/0.63  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.40/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.63  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.40/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.63  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.40/0.63  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.40/0.63  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.40/0.63  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.40/0.63  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.40/0.63  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.40/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.63  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.40/0.63  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.40/0.63  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.40/0.63  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.40/0.63  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.40/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.63  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.40/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.63  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.40/0.63  thf(t17_yellow19, conjecture,
% 0.40/0.63    (![A:$i]:
% 0.40/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.63       ( ![B:$i]:
% 0.40/0.63         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.63             ( v1_subset_1 @
% 0.40/0.63               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.63             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.63             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.63             ( m1_subset_1 @
% 0.40/0.63               B @ 
% 0.40/0.63               ( k1_zfmisc_1 @
% 0.40/0.63                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.63           ( ![C:$i]:
% 0.40/0.63             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.63               ( ( r3_waybel_9 @
% 0.40/0.63                   A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.40/0.63                 ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.40/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.63    (~( ![A:$i]:
% 0.40/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.40/0.63            ( l1_pre_topc @ A ) ) =>
% 0.40/0.63          ( ![B:$i]:
% 0.40/0.63            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.63                ( v1_subset_1 @
% 0.40/0.63                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.63                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.63                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.63                ( m1_subset_1 @
% 0.40/0.63                  B @ 
% 0.40/0.63                  ( k1_zfmisc_1 @
% 0.40/0.63                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.63              ( ![C:$i]:
% 0.40/0.63                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.63                  ( ( r3_waybel_9 @
% 0.40/0.63                      A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.40/0.63                    ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.40/0.63    inference('cnf.neg', [status(esa)], [t17_yellow19])).
% 0.40/0.63  thf('0', plain,
% 0.40/0.63      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.63        | ~ (r3_waybel_9 @ sk_A @ 
% 0.40/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('1', plain,
% 0.40/0.63      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.40/0.63       ~
% 0.40/0.63       ((r3_waybel_9 @ sk_A @ 
% 0.40/0.63         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.63      inference('split', [status(esa)], ['0'])).
% 0.40/0.63  thf('2', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(t30_connsp_2, axiom,
% 0.40/0.63    (![A:$i]:
% 0.40/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.63       ( ![B:$i]:
% 0.40/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.63           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.40/0.63  thf('3', plain,
% 0.40/0.63      (![X13 : $i, X14 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.40/0.63          | (r2_hidden @ X13 @ (k1_connsp_2 @ X14 @ X13))
% 0.40/0.63          | ~ (l1_pre_topc @ X14)
% 0.40/0.63          | ~ (v2_pre_topc @ X14)
% 0.40/0.63          | (v2_struct_0 @ X14))),
% 0.40/0.63      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.40/0.63  thf('4', plain,
% 0.40/0.63      (((v2_struct_0 @ sk_A)
% 0.40/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.40/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.40/0.63        | (r2_hidden @ sk_C @ (k1_connsp_2 @ sk_A @ sk_C)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.63  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('7', plain,
% 0.40/0.63      (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_C @ (k1_connsp_2 @ sk_A @ sk_C)))),
% 0.40/0.63      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.40/0.63  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('9', plain, ((r2_hidden @ sk_C @ (k1_connsp_2 @ sk_A @ sk_C))),
% 0.40/0.63      inference('clc', [status(thm)], ['7', '8'])).
% 0.40/0.63  thf(dt_l1_pre_topc, axiom,
% 0.40/0.63    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.40/0.63  thf('10', plain,
% 0.40/0.63      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.40/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.63  thf('11', plain,
% 0.40/0.63      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.40/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.63  thf(d10_xboole_0, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.63  thf('12', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.63  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.40/0.63      inference('simplify', [status(thm)], ['12'])).
% 0.40/0.63  thf(t3_subset, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.63  thf('14', plain,
% 0.40/0.63      (![X3 : $i, X5 : $i]:
% 0.40/0.63         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.40/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.63  thf('15', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.63  thf('16', plain,
% 0.40/0.63      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.40/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.63  thf(d3_struct_0, axiom,
% 0.40/0.63    (![A:$i]:
% 0.40/0.63     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.40/0.63  thf('17', plain,
% 0.40/0.63      (![X9 : $i]:
% 0.40/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.40/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.63  thf('18', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_B @ 
% 0.40/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(d2_yellow_1, axiom,
% 0.40/0.63    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.40/0.63  thf('19', plain,
% 0.40/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.63  thf('20', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_B @ 
% 0.40/0.63        (k1_zfmisc_1 @ 
% 0.40/0.63         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.63      inference('demod', [status(thm)], ['18', '19'])).
% 0.40/0.63  thf('21', plain,
% 0.40/0.63      (((m1_subset_1 @ sk_B @ 
% 0.40/0.63         (k1_zfmisc_1 @ 
% 0.40/0.63          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 0.40/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.63      inference('sup+', [status(thm)], ['17', '20'])).
% 0.40/0.63  thf('22', plain,
% 0.40/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.63        | (m1_subset_1 @ sk_B @ 
% 0.40/0.63           (k1_zfmisc_1 @ 
% 0.40/0.63            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))))),
% 0.40/0.63      inference('sup-', [status(thm)], ['16', '21'])).
% 0.40/0.63  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('24', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_B @ 
% 0.40/0.63        (k1_zfmisc_1 @ 
% 0.40/0.63         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.40/0.63      inference('demod', [status(thm)], ['22', '23'])).
% 0.40/0.63  thf(fc5_yellow19, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i]:
% 0.40/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.40/0.63         ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.40/0.63         ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.63         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.40/0.63         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.63         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.63         ( m1_subset_1 @
% 0.40/0.63           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.40/0.63       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.40/0.63         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.40/0.63         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.40/0.63  thf('25', plain,
% 0.40/0.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.40/0.63          | (v1_xboole_0 @ X22)
% 0.40/0.63          | ~ (l1_struct_0 @ X23)
% 0.40/0.63          | (v2_struct_0 @ X23)
% 0.40/0.63          | (v1_xboole_0 @ X24)
% 0.40/0.63          | ~ (v1_subset_1 @ X24 @ (u1_struct_0 @ (k3_yellow_1 @ X22)))
% 0.40/0.63          | ~ (v2_waybel_0 @ X24 @ (k3_yellow_1 @ X22))
% 0.40/0.63          | ~ (v13_waybel_0 @ X24 @ (k3_yellow_1 @ X22))
% 0.40/0.63          | ~ (m1_subset_1 @ X24 @ 
% 0.40/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X22))))
% 0.40/0.63          | (v7_waybel_0 @ (k3_yellow19 @ X23 @ X22 @ X24)))),
% 0.40/0.63      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.40/0.63  thf('26', plain,
% 0.40/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.63  thf('27', plain,
% 0.40/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.63  thf('28', plain,
% 0.40/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.63  thf('29', plain,
% 0.40/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.63  thf('30', plain,
% 0.40/0.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.40/0.63          | (v1_xboole_0 @ X22)
% 0.40/0.63          | ~ (l1_struct_0 @ X23)
% 0.40/0.63          | (v2_struct_0 @ X23)
% 0.40/0.63          | (v1_xboole_0 @ X24)
% 0.40/0.63          | ~ (v1_subset_1 @ X24 @ 
% 0.40/0.63               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X22))))
% 0.40/0.63          | ~ (v2_waybel_0 @ X24 @ (k3_lattice3 @ (k1_lattice3 @ X22)))
% 0.40/0.63          | ~ (v13_waybel_0 @ X24 @ (k3_lattice3 @ (k1_lattice3 @ X22)))
% 0.40/0.63          | ~ (m1_subset_1 @ X24 @ 
% 0.40/0.63               (k1_zfmisc_1 @ 
% 0.40/0.63                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X22)))))
% 0.40/0.63          | (v7_waybel_0 @ (k3_yellow19 @ X23 @ X22 @ X24)))),
% 0.40/0.63      inference('demod', [status(thm)], ['25', '26', '27', '28', '29'])).
% 0.40/0.63  thf('31', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.63               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.63          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.63               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.63          | ~ (v1_subset_1 @ sk_B @ 
% 0.40/0.63               (u1_struct_0 @ 
% 0.40/0.63                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.40/0.63          | (v1_xboole_0 @ sk_B)
% 0.40/0.63          | (v2_struct_0 @ X0)
% 0.40/0.63          | ~ (l1_struct_0 @ X0)
% 0.40/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.63      inference('sup-', [status(thm)], ['24', '30'])).
% 0.40/0.63  thf('32', plain,
% 0.40/0.63      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.40/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.63  thf('33', plain,
% 0.40/0.63      (![X9 : $i]:
% 0.40/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.40/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.63  thf('34', plain,
% 0.40/0.63      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('35', plain,
% 0.40/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.63  thf('36', plain,
% 0.40/0.63      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.63        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.63  thf('37', plain,
% 0.40/0.63      (((v13_waybel_0 @ sk_B @ 
% 0.40/0.63         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.63      inference('sup+', [status(thm)], ['33', '36'])).
% 0.40/0.63  thf('38', plain,
% 0.40/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.63        | (v13_waybel_0 @ sk_B @ 
% 0.40/0.63           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.63      inference('sup-', [status(thm)], ['32', '37'])).
% 0.40/0.63  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('40', plain,
% 0.40/0.63      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.63        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.63      inference('demod', [status(thm)], ['38', '39'])).
% 0.40/0.63  thf('41', plain,
% 0.40/0.63      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.40/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.63  thf('42', plain,
% 0.40/0.63      (![X9 : $i]:
% 0.40/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.40/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.63  thf('43', plain,
% 0.40/0.63      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('44', plain,
% 0.40/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.63  thf('45', plain,
% 0.40/0.63      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.63        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.63      inference('demod', [status(thm)], ['43', '44'])).
% 0.40/0.63  thf('46', plain,
% 0.40/0.63      (((v2_waybel_0 @ sk_B @ 
% 0.40/0.63         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.63      inference('sup+', [status(thm)], ['42', '45'])).
% 0.40/0.63  thf('47', plain,
% 0.40/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.63        | (v2_waybel_0 @ sk_B @ 
% 0.40/0.63           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.63      inference('sup-', [status(thm)], ['41', '46'])).
% 0.40/0.63  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('49', plain,
% 0.40/0.63      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.63        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.63      inference('demod', [status(thm)], ['47', '48'])).
% 0.40/0.63  thf('50', plain,
% 0.40/0.63      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.40/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.63  thf('51', plain,
% 0.40/0.63      (![X9 : $i]:
% 0.40/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.40/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.63  thf('52', plain,
% 0.40/0.63      ((v1_subset_1 @ sk_B @ 
% 0.40/0.63        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('53', plain,
% 0.40/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.63  thf('54', plain,
% 0.40/0.63      ((v1_subset_1 @ sk_B @ 
% 0.40/0.63        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.63      inference('demod', [status(thm)], ['52', '53'])).
% 0.40/0.63  thf('55', plain,
% 0.40/0.63      (((v1_subset_1 @ sk_B @ 
% 0.40/0.63         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.40/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.63      inference('sup+', [status(thm)], ['51', '54'])).
% 0.40/0.63  thf('56', plain,
% 0.40/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.63        | (v1_subset_1 @ sk_B @ 
% 0.40/0.63           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.40/0.63      inference('sup-', [status(thm)], ['50', '55'])).
% 0.40/0.63  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('58', plain,
% 0.40/0.63      ((v1_subset_1 @ sk_B @ 
% 0.40/0.63        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.63      inference('demod', [status(thm)], ['56', '57'])).
% 0.40/0.63  thf('59', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63          | (v1_xboole_0 @ sk_B)
% 0.40/0.63          | (v2_struct_0 @ X0)
% 0.40/0.63          | ~ (l1_struct_0 @ X0)
% 0.40/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.63      inference('demod', [status(thm)], ['31', '40', '49', '58'])).
% 0.40/0.63  thf('60', plain,
% 0.40/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.63        | (v2_struct_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['15', '59'])).
% 0.40/0.63  thf('61', plain,
% 0.40/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.63        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v2_struct_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['11', '60'])).
% 0.40/0.63  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('63', plain,
% 0.40/0.63      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v2_struct_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.63      inference('demod', [status(thm)], ['61', '62'])).
% 0.40/0.63  thf('64', plain,
% 0.40/0.63      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.40/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.63  thf('65', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.63  thf('66', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_B @ 
% 0.40/0.63        (k1_zfmisc_1 @ 
% 0.40/0.63         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.40/0.63      inference('demod', [status(thm)], ['22', '23'])).
% 0.40/0.63  thf(fc4_yellow19, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i]:
% 0.40/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.40/0.63         ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.40/0.63         ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.63         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.63         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.63         ( m1_subset_1 @
% 0.40/0.63           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.40/0.63       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.40/0.63         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.40/0.63         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.40/0.63         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.40/0.63  thf('67', plain,
% 0.40/0.63      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.40/0.63          | (v1_xboole_0 @ X19)
% 0.40/0.63          | ~ (l1_struct_0 @ X20)
% 0.40/0.63          | (v2_struct_0 @ X20)
% 0.40/0.63          | (v1_xboole_0 @ X21)
% 0.40/0.63          | ~ (v2_waybel_0 @ X21 @ (k3_yellow_1 @ X19))
% 0.40/0.63          | ~ (v13_waybel_0 @ X21 @ (k3_yellow_1 @ X19))
% 0.40/0.63          | ~ (m1_subset_1 @ X21 @ 
% 0.40/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X19))))
% 0.40/0.63          | (v4_orders_2 @ (k3_yellow19 @ X20 @ X19 @ X21)))),
% 0.40/0.63      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.40/0.63  thf('68', plain,
% 0.40/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.63  thf('69', plain,
% 0.40/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.63  thf('70', plain,
% 0.40/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.63  thf('71', plain,
% 0.40/0.63      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.40/0.63          | (v1_xboole_0 @ X19)
% 0.40/0.63          | ~ (l1_struct_0 @ X20)
% 0.40/0.63          | (v2_struct_0 @ X20)
% 0.40/0.63          | (v1_xboole_0 @ X21)
% 0.40/0.63          | ~ (v2_waybel_0 @ X21 @ (k3_lattice3 @ (k1_lattice3 @ X19)))
% 0.40/0.63          | ~ (v13_waybel_0 @ X21 @ (k3_lattice3 @ (k1_lattice3 @ X19)))
% 0.40/0.63          | ~ (m1_subset_1 @ X21 @ 
% 0.40/0.63               (k1_zfmisc_1 @ 
% 0.40/0.63                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X19)))))
% 0.40/0.63          | (v4_orders_2 @ (k3_yellow19 @ X20 @ X19 @ X21)))),
% 0.40/0.63      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 0.40/0.63  thf('72', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.63               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.63          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.63               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.63          | (v1_xboole_0 @ sk_B)
% 0.40/0.63          | (v2_struct_0 @ X0)
% 0.40/0.63          | ~ (l1_struct_0 @ X0)
% 0.40/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.63      inference('sup-', [status(thm)], ['66', '71'])).
% 0.40/0.63  thf('73', plain,
% 0.40/0.63      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.63        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.63      inference('demod', [status(thm)], ['38', '39'])).
% 0.40/0.63  thf('74', plain,
% 0.40/0.63      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.63        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.63      inference('demod', [status(thm)], ['47', '48'])).
% 0.40/0.63  thf('75', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63          | (v1_xboole_0 @ sk_B)
% 0.40/0.63          | (v2_struct_0 @ X0)
% 0.40/0.63          | ~ (l1_struct_0 @ X0)
% 0.40/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.63      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.40/0.63  thf('76', plain,
% 0.40/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.63        | (v2_struct_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['65', '75'])).
% 0.40/0.63  thf('77', plain,
% 0.40/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.63        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v2_struct_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['64', '76'])).
% 0.40/0.63  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('79', plain,
% 0.40/0.63      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v2_struct_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.63      inference('demod', [status(thm)], ['77', '78'])).
% 0.40/0.63  thf('80', plain,
% 0.40/0.63      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.40/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.63  thf('81', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.63  thf('82', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_B @ 
% 0.40/0.63        (k1_zfmisc_1 @ 
% 0.40/0.63         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.40/0.63      inference('demod', [status(thm)], ['22', '23'])).
% 0.40/0.63  thf(dt_k3_yellow19, axiom,
% 0.40/0.63    (![A:$i,B:$i,C:$i]:
% 0.40/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.40/0.63         ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.40/0.63         ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.63         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.63         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.63         ( m1_subset_1 @
% 0.40/0.63           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.40/0.63       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.40/0.63         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.40/0.63         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.40/0.63  thf('83', plain,
% 0.40/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.40/0.63          | (v1_xboole_0 @ X16)
% 0.40/0.63          | ~ (l1_struct_0 @ X17)
% 0.40/0.63          | (v2_struct_0 @ X17)
% 0.40/0.63          | (v1_xboole_0 @ X18)
% 0.40/0.63          | ~ (v2_waybel_0 @ X18 @ (k3_yellow_1 @ X16))
% 0.40/0.63          | ~ (v13_waybel_0 @ X18 @ (k3_yellow_1 @ X16))
% 0.40/0.63          | ~ (m1_subset_1 @ X18 @ 
% 0.40/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X16))))
% 0.40/0.63          | (l1_waybel_0 @ (k3_yellow19 @ X17 @ X16 @ X18) @ X17))),
% 0.40/0.63      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.40/0.63  thf('84', plain,
% 0.40/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.63  thf('85', plain,
% 0.40/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.63  thf('86', plain,
% 0.40/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.63  thf('87', plain,
% 0.40/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.40/0.63         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.40/0.63          | (v1_xboole_0 @ X16)
% 0.40/0.63          | ~ (l1_struct_0 @ X17)
% 0.40/0.63          | (v2_struct_0 @ X17)
% 0.40/0.63          | (v1_xboole_0 @ X18)
% 0.40/0.63          | ~ (v2_waybel_0 @ X18 @ (k3_lattice3 @ (k1_lattice3 @ X16)))
% 0.40/0.63          | ~ (v13_waybel_0 @ X18 @ (k3_lattice3 @ (k1_lattice3 @ X16)))
% 0.40/0.63          | ~ (m1_subset_1 @ X18 @ 
% 0.40/0.63               (k1_zfmisc_1 @ 
% 0.40/0.63                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X16)))))
% 0.40/0.63          | (l1_waybel_0 @ (k3_yellow19 @ X17 @ X16 @ X18) @ X17))),
% 0.40/0.63      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 0.40/0.63  thf('88', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.63          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.63               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.63          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.63               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.63          | (v1_xboole_0 @ sk_B)
% 0.40/0.63          | (v2_struct_0 @ X0)
% 0.40/0.63          | ~ (l1_struct_0 @ X0)
% 0.40/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.63      inference('sup-', [status(thm)], ['82', '87'])).
% 0.40/0.63  thf('89', plain,
% 0.40/0.63      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.63        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.63      inference('demod', [status(thm)], ['38', '39'])).
% 0.40/0.63  thf('90', plain,
% 0.40/0.63      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.63        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.63      inference('demod', [status(thm)], ['47', '48'])).
% 0.40/0.63  thf('91', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.63          | (v1_xboole_0 @ sk_B)
% 0.40/0.63          | (v2_struct_0 @ X0)
% 0.40/0.63          | ~ (l1_struct_0 @ X0)
% 0.40/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.63      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.40/0.63  thf('92', plain,
% 0.40/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.63        | (v2_struct_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.63           sk_A))),
% 0.40/0.63      inference('sup-', [status(thm)], ['81', '91'])).
% 0.40/0.63  thf('93', plain,
% 0.40/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.63        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.63           sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v2_struct_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['80', '92'])).
% 0.40/0.63  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('95', plain,
% 0.40/0.63      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.63         sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | (v2_struct_0 @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.63      inference('demod', [status(thm)], ['93', '94'])).
% 0.40/0.63  thf('96', plain,
% 0.40/0.63      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.40/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.63  thf('97', plain,
% 0.40/0.63      (![X9 : $i]:
% 0.40/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.40/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.63  thf('98', plain,
% 0.40/0.63      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.63        | (r3_waybel_9 @ sk_A @ 
% 0.40/0.63           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('99', plain,
% 0.40/0.63      (((r3_waybel_9 @ sk_A @ 
% 0.40/0.63         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.40/0.63         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.63      inference('split', [status(esa)], ['98'])).
% 0.40/0.63  thf('100', plain,
% 0.40/0.63      ((((r3_waybel_9 @ sk_A @ 
% 0.40/0.63          (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.40/0.63         | ~ (l1_struct_0 @ sk_A)))
% 0.40/0.63         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.63      inference('sup+', [status(thm)], ['97', '99'])).
% 0.40/0.63  thf('101', plain,
% 0.40/0.63      (((~ (l1_pre_topc @ sk_A)
% 0.40/0.63         | (r3_waybel_9 @ sk_A @ 
% 0.40/0.63            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C)))
% 0.40/0.63         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['96', '100'])).
% 0.40/0.63  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('103', plain,
% 0.40/0.63      (((r3_waybel_9 @ sk_A @ 
% 0.40/0.63         (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.40/0.63         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.63      inference('demod', [status(thm)], ['101', '102'])).
% 0.40/0.63  thf('104', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(t12_yellow19, axiom,
% 0.40/0.63    (![A:$i]:
% 0.40/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.63       ( ![B:$i]:
% 0.40/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.40/0.63             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.40/0.63           ( ![C:$i]:
% 0.40/0.63             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.63               ( ( r3_waybel_9 @ A @ B @ C ) <=>
% 0.40/0.63                 ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.40/0.63  thf('105', plain,
% 0.40/0.63      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.40/0.63         ((v2_struct_0 @ X25)
% 0.40/0.63          | ~ (v4_orders_2 @ X25)
% 0.40/0.63          | ~ (v7_waybel_0 @ X25)
% 0.40/0.63          | ~ (l1_waybel_0 @ X25 @ X26)
% 0.40/0.63          | ~ (r3_waybel_9 @ X26 @ X25 @ X27)
% 0.40/0.63          | (r1_waybel_7 @ X26 @ (k2_yellow19 @ X26 @ X25) @ X27)
% 0.40/0.63          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 0.40/0.63          | ~ (l1_pre_topc @ X26)
% 0.40/0.63          | ~ (v2_pre_topc @ X26)
% 0.40/0.63          | (v2_struct_0 @ X26))),
% 0.40/0.63      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.40/0.63  thf('106', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((v2_struct_0 @ sk_A)
% 0.40/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.40/0.63          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.40/0.63          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.40/0.63          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.40/0.63          | ~ (v7_waybel_0 @ X0)
% 0.40/0.63          | ~ (v4_orders_2 @ X0)
% 0.40/0.63          | (v2_struct_0 @ X0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['104', '105'])).
% 0.40/0.63  thf('107', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('109', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((v2_struct_0 @ sk_A)
% 0.40/0.63          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.40/0.63          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.40/0.63          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.40/0.63          | ~ (v7_waybel_0 @ X0)
% 0.40/0.63          | ~ (v4_orders_2 @ X0)
% 0.40/0.63          | (v2_struct_0 @ X0))),
% 0.40/0.63      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.40/0.63  thf('110', plain,
% 0.40/0.63      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63         | ~ (l1_waybel_0 @ 
% 0.40/0.63              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.40/0.63         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.63            (k2_yellow19 @ sk_A @ 
% 0.40/0.63             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.63            sk_C)
% 0.40/0.63         | (v2_struct_0 @ sk_A)))
% 0.40/0.63         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['103', '109'])).
% 0.40/0.63  thf('111', plain,
% 0.40/0.63      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.63         | (v2_struct_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ sk_B)
% 0.40/0.63         | (v2_struct_0 @ sk_A)
% 0.40/0.63         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.63            (k2_yellow19 @ sk_A @ 
% 0.40/0.63             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.63            sk_C)
% 0.40/0.63         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.63         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['95', '110'])).
% 0.40/0.63  thf('112', plain,
% 0.40/0.63      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.63            (k2_yellow19 @ sk_A @ 
% 0.40/0.63             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.63            sk_C)
% 0.40/0.63         | (v1_xboole_0 @ sk_B)
% 0.40/0.63         | (v2_struct_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.63         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.63      inference('simplify', [status(thm)], ['111'])).
% 0.40/0.63  thf('113', plain,
% 0.40/0.63      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.63         | (v2_struct_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ sk_B)
% 0.40/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.63         | (v2_struct_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ sk_B)
% 0.40/0.63         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.63            (k2_yellow19 @ sk_A @ 
% 0.40/0.63             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.63            sk_C)
% 0.40/0.63         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.63         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['79', '112'])).
% 0.40/0.63  thf('114', plain,
% 0.40/0.63      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.40/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.63  thf('115', plain,
% 0.40/0.63      (![X9 : $i]:
% 0.40/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.40/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.63  thf('116', plain,
% 0.40/0.63      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.40/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.63  thf('117', plain,
% 0.40/0.63      ((m1_subset_1 @ sk_B @ 
% 0.40/0.63        (k1_zfmisc_1 @ 
% 0.40/0.63         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.63      inference('demod', [status(thm)], ['18', '19'])).
% 0.40/0.63  thf(t15_yellow19, axiom,
% 0.40/0.63    (![A:$i]:
% 0.40/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.40/0.63       ( ![B:$i]:
% 0.40/0.63         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.63             ( v1_subset_1 @
% 0.40/0.63               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.63             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.63             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.63             ( m1_subset_1 @
% 0.40/0.63               B @ 
% 0.40/0.63               ( k1_zfmisc_1 @
% 0.40/0.63                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.63           ( ( B ) =
% 0.40/0.63             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.40/0.63  thf('118', plain,
% 0.40/0.63      (![X28 : $i, X29 : $i]:
% 0.40/0.63         ((v1_xboole_0 @ X28)
% 0.40/0.63          | ~ (v1_subset_1 @ X28 @ 
% 0.40/0.63               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X29))))
% 0.40/0.63          | ~ (v2_waybel_0 @ X28 @ (k3_yellow_1 @ (k2_struct_0 @ X29)))
% 0.40/0.63          | ~ (v13_waybel_0 @ X28 @ (k3_yellow_1 @ (k2_struct_0 @ X29)))
% 0.40/0.63          | ~ (m1_subset_1 @ X28 @ 
% 0.40/0.63               (k1_zfmisc_1 @ 
% 0.40/0.63                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X29)))))
% 0.40/0.63          | ((X28)
% 0.40/0.63              = (k2_yellow19 @ X29 @ 
% 0.40/0.63                 (k3_yellow19 @ X29 @ (k2_struct_0 @ X29) @ X28)))
% 0.40/0.63          | ~ (l1_struct_0 @ X29)
% 0.40/0.63          | (v2_struct_0 @ X29))),
% 0.40/0.63      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.40/0.63  thf('119', plain,
% 0.40/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.63  thf('120', plain,
% 0.40/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.63  thf('121', plain,
% 0.40/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.63  thf('122', plain,
% 0.40/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.63  thf('123', plain,
% 0.40/0.63      (![X28 : $i, X29 : $i]:
% 0.40/0.63         ((v1_xboole_0 @ X28)
% 0.40/0.63          | ~ (v1_subset_1 @ X28 @ 
% 0.40/0.63               (u1_struct_0 @ 
% 0.40/0.63                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29)))))
% 0.40/0.63          | ~ (v2_waybel_0 @ X28 @ 
% 0.40/0.63               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29))))
% 0.40/0.63          | ~ (v13_waybel_0 @ X28 @ 
% 0.40/0.63               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29))))
% 0.40/0.63          | ~ (m1_subset_1 @ X28 @ 
% 0.40/0.63               (k1_zfmisc_1 @ 
% 0.40/0.63                (u1_struct_0 @ 
% 0.40/0.63                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29))))))
% 0.40/0.63          | ((X28)
% 0.40/0.63              = (k2_yellow19 @ X29 @ 
% 0.40/0.63                 (k3_yellow19 @ X29 @ (k2_struct_0 @ X29) @ X28)))
% 0.40/0.63          | ~ (l1_struct_0 @ X29)
% 0.40/0.63          | (v2_struct_0 @ X29))),
% 0.40/0.63      inference('demod', [status(thm)], ['118', '119', '120', '121', '122'])).
% 0.40/0.63  thf('124', plain,
% 0.40/0.63      (((v2_struct_0 @ sk_A)
% 0.40/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.63        | ((sk_B)
% 0.40/0.63            = (k2_yellow19 @ sk_A @ 
% 0.40/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.63        | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.63             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.63        | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.63             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.63        | ~ (v1_subset_1 @ sk_B @ 
% 0.40/0.63             (u1_struct_0 @ 
% 0.40/0.63              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.40/0.63        | (v1_xboole_0 @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['117', '123'])).
% 0.40/0.63  thf('125', plain,
% 0.40/0.63      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.63        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.63  thf('126', plain,
% 0.40/0.63      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.63        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.63      inference('demod', [status(thm)], ['43', '44'])).
% 0.40/0.63  thf('127', plain,
% 0.40/0.63      ((v1_subset_1 @ sk_B @ 
% 0.40/0.63        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.63      inference('demod', [status(thm)], ['52', '53'])).
% 0.40/0.63  thf('128', plain,
% 0.40/0.63      (((v2_struct_0 @ sk_A)
% 0.40/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.63        | ((sk_B)
% 0.40/0.63            = (k2_yellow19 @ sk_A @ 
% 0.40/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.63        | (v1_xboole_0 @ sk_B))),
% 0.40/0.63      inference('demod', [status(thm)], ['124', '125', '126', '127'])).
% 0.40/0.63  thf('129', plain,
% 0.40/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.63        | (v1_xboole_0 @ sk_B)
% 0.40/0.63        | ((sk_B)
% 0.40/0.63            = (k2_yellow19 @ sk_A @ 
% 0.40/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.63        | (v2_struct_0 @ sk_A))),
% 0.40/0.63      inference('sup-', [status(thm)], ['116', '128'])).
% 0.40/0.63  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('131', plain,
% 0.40/0.63      (((v1_xboole_0 @ sk_B)
% 0.40/0.63        | ((sk_B)
% 0.40/0.63            = (k2_yellow19 @ sk_A @ 
% 0.40/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.63        | (v2_struct_0 @ sk_A))),
% 0.40/0.63      inference('demod', [status(thm)], ['129', '130'])).
% 0.40/0.63  thf('132', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('133', plain,
% 0.40/0.63      (((v2_struct_0 @ sk_A)
% 0.40/0.63        | ((sk_B)
% 0.40/0.63            = (k2_yellow19 @ sk_A @ 
% 0.40/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.40/0.63      inference('clc', [status(thm)], ['131', '132'])).
% 0.40/0.63  thf('134', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('135', plain,
% 0.40/0.63      (((sk_B)
% 0.40/0.63         = (k2_yellow19 @ sk_A @ 
% 0.40/0.63            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.63      inference('clc', [status(thm)], ['133', '134'])).
% 0.40/0.63  thf('136', plain,
% 0.40/0.63      ((((sk_B)
% 0.40/0.63          = (k2_yellow19 @ sk_A @ 
% 0.40/0.63             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.63      inference('sup+', [status(thm)], ['115', '135'])).
% 0.40/0.63  thf('137', plain,
% 0.40/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.63        | ((sk_B)
% 0.40/0.63            = (k2_yellow19 @ sk_A @ 
% 0.40/0.63               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.40/0.63      inference('sup-', [status(thm)], ['114', '136'])).
% 0.40/0.63  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('139', plain,
% 0.40/0.63      (((sk_B)
% 0.40/0.63         = (k2_yellow19 @ sk_A @ 
% 0.40/0.63            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.63      inference('demod', [status(thm)], ['137', '138'])).
% 0.40/0.63  thf('140', plain,
% 0.40/0.63      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.63         | (v2_struct_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ sk_B)
% 0.40/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.63         | (v2_struct_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ sk_B)
% 0.40/0.63         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.63         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.63         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.63      inference('demod', [status(thm)], ['113', '139'])).
% 0.40/0.63  thf('141', plain,
% 0.40/0.63      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.63         | (v1_xboole_0 @ sk_B)
% 0.40/0.63         | (v2_struct_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.63         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.63      inference('simplify', [status(thm)], ['140'])).
% 0.40/0.63  thf('142', plain,
% 0.40/0.63      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.63         | (v2_struct_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ sk_B)
% 0.40/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.63         | (v2_struct_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ sk_B)
% 0.40/0.63         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.63         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['63', '141'])).
% 0.40/0.63  thf('143', plain,
% 0.40/0.63      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.63         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.63         | (v1_xboole_0 @ sk_B)
% 0.40/0.63         | (v2_struct_0 @ sk_A)
% 0.40/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.63         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.63      inference('simplify', [status(thm)], ['142'])).
% 0.40/0.63  thf('144', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.63  thf('145', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B @ 
% 0.47/0.63        (k1_zfmisc_1 @ 
% 0.47/0.63         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.47/0.63      inference('demod', [status(thm)], ['22', '23'])).
% 0.47/0.63  thf('146', plain,
% 0.47/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.47/0.63          | (v1_xboole_0 @ X16)
% 0.47/0.63          | ~ (l1_struct_0 @ X17)
% 0.47/0.63          | (v2_struct_0 @ X17)
% 0.47/0.63          | (v1_xboole_0 @ X18)
% 0.47/0.63          | ~ (v2_waybel_0 @ X18 @ (k3_yellow_1 @ X16))
% 0.47/0.63          | ~ (v13_waybel_0 @ X18 @ (k3_yellow_1 @ X16))
% 0.47/0.63          | ~ (m1_subset_1 @ X18 @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X16))))
% 0.47/0.63          | ~ (v2_struct_0 @ (k3_yellow19 @ X17 @ X16 @ X18)))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.47/0.63  thf('147', plain,
% 0.47/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('148', plain,
% 0.47/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('149', plain,
% 0.47/0.63      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k3_lattice3 @ (k1_lattice3 @ X15)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('150', plain,
% 0.47/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.47/0.63          | (v1_xboole_0 @ X16)
% 0.47/0.63          | ~ (l1_struct_0 @ X17)
% 0.47/0.63          | (v2_struct_0 @ X17)
% 0.47/0.63          | (v1_xboole_0 @ X18)
% 0.47/0.63          | ~ (v2_waybel_0 @ X18 @ (k3_lattice3 @ (k1_lattice3 @ X16)))
% 0.47/0.63          | ~ (v13_waybel_0 @ X18 @ (k3_lattice3 @ (k1_lattice3 @ X16)))
% 0.47/0.63          | ~ (m1_subset_1 @ X18 @ 
% 0.47/0.63               (k1_zfmisc_1 @ 
% 0.47/0.63                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X16)))))
% 0.47/0.63          | ~ (v2_struct_0 @ (k3_yellow19 @ X17 @ X16 @ X18)))),
% 0.47/0.63      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 0.47/0.63  thf('151', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (v13_waybel_0 @ sk_B @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63          | ~ (v2_waybel_0 @ sk_B @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['145', '150'])).
% 0.47/0.63  thf('152', plain,
% 0.47/0.63      ((v13_waybel_0 @ sk_B @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['38', '39'])).
% 0.47/0.63  thf('153', plain,
% 0.47/0.63      ((v2_waybel_0 @ sk_B @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['47', '48'])).
% 0.47/0.63  thf('154', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['151', '152', '153'])).
% 0.47/0.63  thf('155', plain,
% 0.47/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['144', '154'])).
% 0.47/0.63  thf('156', plain,
% 0.47/0.63      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)
% 0.47/0.63         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63         <= (((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['143', '155'])).
% 0.47/0.63  thf('157', plain,
% 0.47/0.63      (((~ (l1_struct_0 @ sk_A)
% 0.47/0.63         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63         <= (((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.47/0.63      inference('simplify', [status(thm)], ['156'])).
% 0.47/0.63  thf('158', plain,
% 0.47/0.63      (((~ (l1_pre_topc @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)
% 0.47/0.63         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.47/0.63         <= (((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['10', '157'])).
% 0.47/0.63  thf('159', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('160', plain,
% 0.47/0.63      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)
% 0.47/0.63         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.47/0.63         <= (((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.47/0.63      inference('demod', [status(thm)], ['158', '159'])).
% 0.47/0.63  thf('161', plain,
% 0.47/0.63      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.47/0.63         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('split', [status(esa)], ['0'])).
% 0.47/0.63  thf('162', plain,
% 0.47/0.63      ((((v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.47/0.63             ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['160', '161'])).
% 0.47/0.63  thf('163', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('164', plain,
% 0.47/0.63      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.47/0.63         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.47/0.63             ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.47/0.63      inference('clc', [status(thm)], ['162', '163'])).
% 0.47/0.63  thf('165', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('166', plain,
% 0.47/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.47/0.63         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.47/0.63             ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.47/0.63      inference('clc', [status(thm)], ['164', '165'])).
% 0.47/0.63  thf('167', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(dt_k1_connsp_2, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.63         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.63       ( m1_subset_1 @
% 0.47/0.63         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.47/0.63  thf('168', plain,
% 0.47/0.63      (![X11 : $i, X12 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ X11)
% 0.47/0.63          | ~ (v2_pre_topc @ X11)
% 0.47/0.63          | (v2_struct_0 @ X11)
% 0.47/0.63          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.47/0.63          | (m1_subset_1 @ (k1_connsp_2 @ X11 @ X12) @ 
% 0.47/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.47/0.63  thf('169', plain,
% 0.47/0.63      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_C) @ 
% 0.47/0.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['167', '168'])).
% 0.47/0.63  thf('170', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('171', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('172', plain,
% 0.47/0.63      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_C) @ 
% 0.47/0.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.63        | (v2_struct_0 @ sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['169', '170', '171'])).
% 0.47/0.63  thf('173', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('174', plain,
% 0.47/0.63      ((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_C) @ 
% 0.47/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('clc', [status(thm)], ['172', '173'])).
% 0.47/0.63  thf(t5_subset, axiom,
% 0.47/0.63    (![A:$i,B:$i,C:$i]:
% 0.47/0.63     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.47/0.63          ( v1_xboole_0 @ C ) ) ))).
% 0.47/0.63  thf('175', plain,
% 0.47/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X6 @ X7)
% 0.47/0.63          | ~ (v1_xboole_0 @ X8)
% 0.47/0.63          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.47/0.63      inference('cnf', [status(esa)], [t5_subset])).
% 0.47/0.63  thf('176', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_A @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['174', '175'])).
% 0.47/0.63  thf('177', plain,
% 0.47/0.63      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_A @ sk_C)))
% 0.47/0.63         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.47/0.63             ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['166', '176'])).
% 0.47/0.63  thf('178', plain,
% 0.47/0.63      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.47/0.63       ~
% 0.47/0.63       ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.47/0.63      inference('sup-', [status(thm)], ['9', '177'])).
% 0.47/0.63  thf('179', plain,
% 0.47/0.63      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.47/0.63       ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.47/0.63      inference('split', [status(esa)], ['98'])).
% 0.47/0.63  thf('180', plain, ((r2_hidden @ sk_C @ (k1_connsp_2 @ sk_A @ sk_C))),
% 0.47/0.63      inference('clc', [status(thm)], ['7', '8'])).
% 0.47/0.63  thf('181', plain,
% 0.47/0.63      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('182', plain,
% 0.47/0.63      (![X9 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.63  thf('183', plain,
% 0.47/0.63      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('184', plain,
% 0.47/0.63      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.47/0.63         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('split', [status(esa)], ['98'])).
% 0.47/0.63  thf('185', plain,
% 0.47/0.63      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('186', plain,
% 0.47/0.63      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['61', '62'])).
% 0.47/0.63  thf('187', plain,
% 0.47/0.63      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['77', '78'])).
% 0.47/0.63  thf('188', plain,
% 0.47/0.63      (![X9 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.63  thf('189', plain,
% 0.47/0.63      (![X9 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.63  thf('190', plain,
% 0.47/0.63      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.47/0.63         sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['93', '94'])).
% 0.47/0.63  thf('191', plain,
% 0.47/0.63      (![X9 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.63  thf('192', plain,
% 0.47/0.63      (((sk_B)
% 0.47/0.63         = (k2_yellow19 @ sk_A @ 
% 0.47/0.63            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('clc', [status(thm)], ['133', '134'])).
% 0.47/0.63  thf('193', plain,
% 0.47/0.63      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.63         ((v2_struct_0 @ X25)
% 0.47/0.63          | ~ (v4_orders_2 @ X25)
% 0.47/0.63          | ~ (v7_waybel_0 @ X25)
% 0.47/0.63          | ~ (l1_waybel_0 @ X25 @ X26)
% 0.47/0.63          | ~ (r1_waybel_7 @ X26 @ (k2_yellow19 @ X26 @ X25) @ X27)
% 0.47/0.63          | (r3_waybel_9 @ X26 @ X25 @ X27)
% 0.47/0.63          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 0.47/0.63          | ~ (l1_pre_topc @ X26)
% 0.47/0.63          | ~ (v2_pre_topc @ X26)
% 0.47/0.63          | (v2_struct_0 @ X26))),
% 0.47/0.63      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.47/0.63  thf('194', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r3_waybel_9 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.47/0.63          | ~ (l1_waybel_0 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.47/0.63          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['192', '193'])).
% 0.47/0.63  thf('195', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('196', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('197', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r3_waybel_9 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.47/0.63          | ~ (l1_waybel_0 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.47/0.63          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('demod', [status(thm)], ['194', '195', '196'])).
% 0.47/0.63  thf('198', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_waybel_0 @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (r3_waybel_9 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['191', '197'])).
% 0.47/0.63  thf('199', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r3_waybel_9 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.47/0.63          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['190', '198'])).
% 0.47/0.63  thf('200', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (r3_waybel_9 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('simplify', [status(thm)], ['199'])).
% 0.47/0.63  thf('201', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r3_waybel_9 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.47/0.63          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['189', '200'])).
% 0.47/0.63  thf('202', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (r3_waybel_9 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('simplify', [status(thm)], ['201'])).
% 0.47/0.63  thf('203', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r3_waybel_9 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['188', '202'])).
% 0.47/0.63  thf('204', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (r3_waybel_9 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('simplify', [status(thm)], ['203'])).
% 0.47/0.63  thf('205', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r3_waybel_9 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['187', '204'])).
% 0.47/0.63  thf('206', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (r3_waybel_9 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('simplify', [status(thm)], ['205'])).
% 0.47/0.63  thf('207', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r3_waybel_9 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['186', '206'])).
% 0.47/0.63  thf('208', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (r3_waybel_9 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('simplify', [status(thm)], ['207'])).
% 0.47/0.63  thf('209', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r3_waybel_9 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['185', '208'])).
% 0.47/0.63  thf('210', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('211', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r3_waybel_9 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('demod', [status(thm)], ['209', '210'])).
% 0.47/0.63  thf('212', plain,
% 0.47/0.63      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | (r3_waybel_9 @ sk_A @ 
% 0.47/0.63            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.47/0.63         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | (v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['184', '211'])).
% 0.47/0.63  thf('213', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('214', plain,
% 0.47/0.63      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | (r3_waybel_9 @ sk_A @ 
% 0.47/0.63            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('demod', [status(thm)], ['212', '213'])).
% 0.47/0.63  thf('215', plain,
% 0.47/0.63      ((~ (r3_waybel_9 @ sk_A @ 
% 0.47/0.63           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.47/0.63      inference('split', [status(esa)], ['0'])).
% 0.47/0.63  thf('216', plain,
% 0.47/0.63      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.47/0.63             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['214', '215'])).
% 0.47/0.63  thf('217', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.63  thf('218', plain,
% 0.47/0.63      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('219', plain,
% 0.47/0.63      (![X9 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.63  thf('220', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B @ 
% 0.47/0.63        (k1_zfmisc_1 @ 
% 0.47/0.63         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.47/0.63      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.63  thf('221', plain,
% 0.47/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.47/0.63          | (v1_xboole_0 @ X16)
% 0.47/0.63          | ~ (l1_struct_0 @ X17)
% 0.47/0.63          | (v2_struct_0 @ X17)
% 0.47/0.63          | (v1_xboole_0 @ X18)
% 0.47/0.63          | ~ (v2_waybel_0 @ X18 @ (k3_lattice3 @ (k1_lattice3 @ X16)))
% 0.47/0.63          | ~ (v13_waybel_0 @ X18 @ (k3_lattice3 @ (k1_lattice3 @ X16)))
% 0.47/0.63          | ~ (m1_subset_1 @ X18 @ 
% 0.47/0.63               (k1_zfmisc_1 @ 
% 0.47/0.63                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X16)))))
% 0.47/0.63          | ~ (v2_struct_0 @ (k3_yellow19 @ X17 @ X16 @ X18)))),
% 0.47/0.63      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 0.47/0.63  thf('222', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (v13_waybel_0 @ sk_B @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63          | ~ (v2_waybel_0 @ sk_B @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['220', '221'])).
% 0.47/0.63  thf('223', plain,
% 0.47/0.63      ((v13_waybel_0 @ sk_B @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.47/0.63  thf('224', plain,
% 0.47/0.63      ((v2_waybel_0 @ sk_B @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['43', '44'])).
% 0.47/0.63  thf('225', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['222', '223', '224'])).
% 0.47/0.63  thf('226', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['219', '225'])).
% 0.47/0.63  thf('227', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ sk_A)
% 0.47/0.63          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['218', '226'])).
% 0.47/0.63  thf('228', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('229', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['227', '228'])).
% 0.47/0.63  thf('230', plain,
% 0.47/0.63      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['217', '229'])).
% 0.47/0.63  thf('231', plain,
% 0.47/0.63      ((((v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | (v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.47/0.63             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['216', '230'])).
% 0.47/0.63  thf('232', plain,
% 0.47/0.63      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.47/0.63             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('simplify', [status(thm)], ['231'])).
% 0.47/0.63  thf('233', plain,
% 0.47/0.63      (((~ (l1_pre_topc @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.47/0.63             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['183', '232'])).
% 0.47/0.63  thf('234', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('235', plain,
% 0.47/0.63      ((((v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.47/0.63             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('demod', [status(thm)], ['233', '234'])).
% 0.47/0.63  thf('236', plain,
% 0.47/0.63      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.47/0.63             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('sup+', [status(thm)], ['182', '235'])).
% 0.47/0.63  thf('237', plain,
% 0.47/0.63      ((((v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.47/0.63             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('simplify', [status(thm)], ['236'])).
% 0.47/0.63  thf('238', plain,
% 0.47/0.63      (((~ (l1_pre_topc @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.47/0.63             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['181', '237'])).
% 0.47/0.63  thf('239', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('240', plain,
% 0.47/0.63      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.47/0.63             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('demod', [status(thm)], ['238', '239'])).
% 0.47/0.63  thf('241', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('242', plain,
% 0.47/0.63      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.47/0.63             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('clc', [status(thm)], ['240', '241'])).
% 0.47/0.63  thf('243', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('244', plain,
% 0.47/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.47/0.63             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('clc', [status(thm)], ['242', '243'])).
% 0.47/0.63  thf('245', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_A @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['174', '175'])).
% 0.47/0.63  thf('246', plain,
% 0.47/0.63      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_A @ sk_C)))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.47/0.63             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['244', '245'])).
% 0.47/0.63  thf('247', plain,
% 0.47/0.63      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.47/0.63       ((r3_waybel_9 @ sk_A @ 
% 0.47/0.63         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.47/0.63      inference('sup-', [status(thm)], ['180', '246'])).
% 0.47/0.63  thf('248', plain, ($false),
% 0.47/0.63      inference('sat_resolution*', [status(thm)], ['1', '178', '179', '247'])).
% 0.47/0.63  
% 0.47/0.63  % SZS output end Refutation
% 0.47/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
