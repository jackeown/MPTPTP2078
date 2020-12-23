%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uq7BbxdZcU

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:48 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  261 ( 922 expanded)
%              Number of leaves         :   48 ( 305 expanded)
%              Depth                    :   39
%              Number of atoms          : 3370 (18010 expanded)
%              Number of equality atoms :   43 ( 245 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

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
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('2',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('4',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('5',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('9',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('10',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v1_xboole_0 @ X24 )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( v1_subset_1 @ X26 @ ( u1_struct_0 @ ( k3_yellow_1 @ X24 ) ) )
      | ~ ( v2_waybel_0 @ X26 @ ( k3_yellow_1 @ X24 ) )
      | ~ ( v13_waybel_0 @ X26 @ ( k3_yellow_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X24 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X25 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('12',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('13',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('14',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('15',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('16',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v1_xboole_0 @ X24 )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( v1_subset_1 @ X26 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) )
      | ~ ( v2_waybel_0 @ X26 @ ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) )
      | ~ ( v13_waybel_0 @ X26 @ ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X25 @ X24 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('20',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('23',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('26',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['17','20','23','26'])).

thf('28',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['7','27'])).

thf('29',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['6','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('35',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('36',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_xboole_0 @ X21 )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( v2_waybel_0 @ X23 @ ( k3_yellow_1 @ X21 ) )
      | ~ ( v13_waybel_0 @ X23 @ ( k3_yellow_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X21 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X22 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('37',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('38',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('39',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('40',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_xboole_0 @ X21 )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( v2_waybel_0 @ X23 @ ( k3_lattice3 @ ( k1_lattice3 @ X21 ) ) )
      | ~ ( v13_waybel_0 @ X23 @ ( k3_lattice3 @ ( k1_lattice3 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X21 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X22 @ X21 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('43',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['34','44'])).

thf('46',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['33','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('53',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_xboole_0 @ X18 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( v2_waybel_0 @ X20 @ ( k3_yellow_1 @ X18 ) )
      | ~ ( v13_waybel_0 @ X20 @ ( k3_yellow_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X18 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X19 @ X18 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('54',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('55',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('56',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('57',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_xboole_0 @ X18 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( v2_waybel_0 @ X20 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) )
      | ~ ( v13_waybel_0 @ X20 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X19 @ X18 @ X20 ) @ X19 ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('60',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','61'])).

thf('63',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
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

thf('70',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ~ ( v7_waybel_0 @ X27 )
      | ~ ( l1_waybel_0 @ X27 @ X28 )
      | ~ ( r3_waybel_9 @ X28 @ X27 @ X29 )
      | ( r1_waybel_7 @ X28 @ ( k2_yellow19 @ X28 @ X27 ) @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C_1 )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C_1 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C_1 )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C_1 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('77',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('78',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v1_subset_1 @ X30 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X31 ) ) ) )
      | ~ ( v2_waybel_0 @ X30 @ ( k3_yellow_1 @ ( k2_struct_0 @ X31 ) ) )
      | ~ ( v13_waybel_0 @ X30 @ ( k3_yellow_1 @ ( k2_struct_0 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X31 ) ) ) ) )
      | ( X30
        = ( k2_yellow19 @ X31 @ ( k3_yellow19 @ X31 @ ( k2_struct_0 @ X31 ) @ X30 ) ) )
      | ~ ( l1_struct_0 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('79',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('80',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('81',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('82',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('83',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v1_subset_1 @ X30 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X31 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X30 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X31 ) ) ) )
      | ~ ( v13_waybel_0 @ X30 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X31 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X31 ) ) ) ) ) )
      | ( X30
        = ( k2_yellow19 @ X31 @ ( k3_yellow19 @ X31 @ ( k2_struct_0 @ X31 ) @ X30 ) ) )
      | ~ ( l1_struct_0 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('86',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('87',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( sk_B_2
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['75','95'])).

thf('97',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['66','96'])).

thf('98',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','98'])).

thf('100',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','100'])).

thf('102',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('104',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('105',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_xboole_0 @ X18 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( v2_waybel_0 @ X20 @ ( k3_yellow_1 @ X18 ) )
      | ~ ( v13_waybel_0 @ X20 @ ( k3_yellow_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X18 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X19 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('106',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('107',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('108',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('109',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_xboole_0 @ X18 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( v2_waybel_0 @ X20 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) )
      | ~ ( v13_waybel_0 @ X20 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X19 @ X18 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('112',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['103','113'])).

thf('115',plain,
    ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['102','115'])).

thf('117',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
   <= ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('122',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','126'])).

thf('128',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','127'])).

thf('129',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('131',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(rc20_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ? [B: $i] :
          ( ( v1_zfmisc_1 @ B )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('132',plain,(
    ! [X16: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[rc20_struct_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('133',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('135',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['130','139'])).

thf('141',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[rc20_struct_0])).

thf('142',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','144'])).

thf('146',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['67'])).

thf('149',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('150',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('151',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('152',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('153',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
   <= ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['67'])).

thf('154',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('155',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('156',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('157',plain,
    ( sk_B_2
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('158',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ~ ( v7_waybel_0 @ X27 )
      | ~ ( l1_waybel_0 @ X27 @ X28 )
      | ~ ( r1_waybel_7 @ X28 @ ( k2_yellow19 @ X28 @ X27 ) @ X29 )
      | ( r3_waybel_9 @ X28 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['156','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['155','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['154','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['153','168'])).

thf('170',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('173',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['114'])).

thf('175',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['152','176'])).

thf('178',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('182',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['181','182'])).

thf('184',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['151','183'])).

thf('185',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['150','184'])).

thf('186',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('189',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('191',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('194',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( sk_B_1 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['190','195'])).

thf('197',plain,
    ( ( ( ( sk_B_1 @ sk_A )
        = ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['189','196'])).

thf('198',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['197','198'])).

thf('200',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( sk_B_1 @ sk_A )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['188','199'])).

thf('201',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( ( sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['187','202'])).

thf('204',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[rc20_struct_0])).

thf('205',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['205','206'])).

thf('208',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['149','207'])).

thf('209',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','147','148','210'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uq7BbxdZcU
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:06:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.18/1.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.18/1.44  % Solved by: fo/fo7.sh
% 1.18/1.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.18/1.44  % done 990 iterations in 0.978s
% 1.18/1.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.18/1.44  % SZS output start Refutation
% 1.18/1.44  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 1.18/1.44  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 1.18/1.44  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 1.18/1.44  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.18/1.44  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 1.18/1.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.18/1.44  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.18/1.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.18/1.44  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 1.18/1.44  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.18/1.44  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.18/1.44  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 1.18/1.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.18/1.44  thf(sk_B_type, type, sk_B: $i > $i).
% 1.18/1.44  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.18/1.44  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 1.18/1.44  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.18/1.44  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.18/1.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.18/1.44  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 1.18/1.44  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 1.18/1.44  thf(sk_A_type, type, sk_A: $i).
% 1.18/1.44  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 1.18/1.44  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.18/1.44  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 1.18/1.44  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 1.18/1.44  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.18/1.44  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 1.18/1.44  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.18/1.44  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.18/1.44  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 1.18/1.44  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 1.18/1.44  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.18/1.44  thf(t17_yellow19, conjecture,
% 1.18/1.44    (![A:$i]:
% 1.18/1.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.18/1.44       ( ![B:$i]:
% 1.18/1.44         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.18/1.44             ( v1_subset_1 @
% 1.18/1.44               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 1.18/1.44             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.18/1.44             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.18/1.44             ( m1_subset_1 @
% 1.18/1.44               B @ 
% 1.18/1.44               ( k1_zfmisc_1 @
% 1.18/1.44                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 1.18/1.44           ( ![C:$i]:
% 1.18/1.44             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.18/1.44               ( ( r3_waybel_9 @
% 1.18/1.44                   A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 1.18/1.44                 ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 1.18/1.44  thf(zf_stmt_0, negated_conjecture,
% 1.18/1.44    (~( ![A:$i]:
% 1.18/1.44        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.18/1.44            ( l1_pre_topc @ A ) ) =>
% 1.18/1.44          ( ![B:$i]:
% 1.18/1.44            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.18/1.44                ( v1_subset_1 @
% 1.18/1.44                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 1.18/1.44                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.18/1.44                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.18/1.44                ( m1_subset_1 @
% 1.18/1.44                  B @ 
% 1.18/1.44                  ( k1_zfmisc_1 @
% 1.18/1.44                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 1.18/1.44              ( ![C:$i]:
% 1.18/1.44                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.18/1.44                  ( ( r3_waybel_9 @
% 1.18/1.44                      A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 1.18/1.44                    ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 1.18/1.44    inference('cnf.neg', [status(esa)], [t17_yellow19])).
% 1.18/1.44  thf('0', plain,
% 1.18/1.44      ((~ (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)
% 1.18/1.44        | ~ (r3_waybel_9 @ sk_A @ 
% 1.18/1.44             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('1', plain,
% 1.18/1.44      (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) | 
% 1.18/1.44       ~
% 1.18/1.44       ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1))),
% 1.18/1.44      inference('split', [status(esa)], ['0'])).
% 1.18/1.44  thf(dt_l1_pre_topc, axiom,
% 1.18/1.44    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.18/1.44  thf('2', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.18/1.44  thf('3', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.18/1.44  thf(d3_struct_0, axiom,
% 1.18/1.44    (![A:$i]:
% 1.18/1.44     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.18/1.44  thf('4', plain,
% 1.18/1.44      (![X13 : $i]:
% 1.18/1.44         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 1.18/1.44      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.44  thf('5', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.18/1.44  thf('6', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.18/1.44  thf(dt_k2_struct_0, axiom,
% 1.18/1.44    (![A:$i]:
% 1.18/1.44     ( ( l1_struct_0 @ A ) =>
% 1.18/1.44       ( m1_subset_1 @
% 1.18/1.44         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.18/1.44  thf('7', plain,
% 1.18/1.44      (![X14 : $i]:
% 1.18/1.44         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 1.18/1.44           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.18/1.44          | ~ (l1_struct_0 @ X14))),
% 1.18/1.44      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.18/1.44  thf('8', plain,
% 1.18/1.44      ((m1_subset_1 @ sk_B_2 @ 
% 1.18/1.44        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf(d2_yellow_1, axiom,
% 1.18/1.44    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 1.18/1.44  thf('9', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('10', plain,
% 1.18/1.44      ((m1_subset_1 @ sk_B_2 @ 
% 1.18/1.44        (k1_zfmisc_1 @ 
% 1.18/1.44         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.18/1.44      inference('demod', [status(thm)], ['8', '9'])).
% 1.18/1.44  thf(fc5_yellow19, axiom,
% 1.18/1.44    (![A:$i,B:$i,C:$i]:
% 1.18/1.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 1.18/1.44         ( ~( v1_xboole_0 @ B ) ) & 
% 1.18/1.44         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.18/1.44         ( ~( v1_xboole_0 @ C ) ) & 
% 1.18/1.44         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 1.18/1.44         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 1.18/1.44         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 1.18/1.44         ( m1_subset_1 @
% 1.18/1.44           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 1.18/1.44       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 1.18/1.44         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 1.18/1.44         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 1.18/1.44  thf('11', plain,
% 1.18/1.44      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.18/1.44         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.18/1.44          | (v1_xboole_0 @ X24)
% 1.18/1.44          | ~ (l1_struct_0 @ X25)
% 1.18/1.44          | (v2_struct_0 @ X25)
% 1.18/1.44          | (v1_xboole_0 @ X26)
% 1.18/1.44          | ~ (v1_subset_1 @ X26 @ (u1_struct_0 @ (k3_yellow_1 @ X24)))
% 1.18/1.44          | ~ (v2_waybel_0 @ X26 @ (k3_yellow_1 @ X24))
% 1.18/1.44          | ~ (v13_waybel_0 @ X26 @ (k3_yellow_1 @ X24))
% 1.18/1.44          | ~ (m1_subset_1 @ X26 @ 
% 1.18/1.44               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X24))))
% 1.18/1.44          | (v7_waybel_0 @ (k3_yellow19 @ X25 @ X24 @ X26)))),
% 1.18/1.44      inference('cnf', [status(esa)], [fc5_yellow19])).
% 1.18/1.44  thf('12', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('13', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('14', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('15', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('16', plain,
% 1.18/1.44      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.18/1.44         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.18/1.44          | (v1_xboole_0 @ X24)
% 1.18/1.44          | ~ (l1_struct_0 @ X25)
% 1.18/1.44          | (v2_struct_0 @ X25)
% 1.18/1.44          | (v1_xboole_0 @ X26)
% 1.18/1.44          | ~ (v1_subset_1 @ X26 @ 
% 1.18/1.44               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X24))))
% 1.18/1.44          | ~ (v2_waybel_0 @ X26 @ (k3_lattice3 @ (k1_lattice3 @ X24)))
% 1.18/1.44          | ~ (v13_waybel_0 @ X26 @ (k3_lattice3 @ (k1_lattice3 @ X24)))
% 1.18/1.44          | ~ (m1_subset_1 @ X26 @ 
% 1.18/1.44               (k1_zfmisc_1 @ 
% 1.18/1.44                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X24)))))
% 1.18/1.44          | (v7_waybel_0 @ (k3_yellow19 @ X25 @ X24 @ X26)))),
% 1.18/1.44      inference('demod', [status(thm)], ['11', '12', '13', '14', '15'])).
% 1.18/1.44  thf('17', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 1.18/1.44               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.18/1.44          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 1.18/1.44               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.18/1.44          | ~ (v1_subset_1 @ sk_B_2 @ 
% 1.18/1.44               (u1_struct_0 @ 
% 1.18/1.44                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 1.18/1.44          | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44          | (v2_struct_0 @ X0)
% 1.18/1.44          | ~ (l1_struct_0 @ X0)
% 1.18/1.44          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.18/1.44               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.18/1.44      inference('sup-', [status(thm)], ['10', '16'])).
% 1.18/1.44  thf('18', plain,
% 1.18/1.44      ((v13_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('19', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('20', plain,
% 1.18/1.44      ((v13_waybel_0 @ sk_B_2 @ 
% 1.18/1.44        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.18/1.44      inference('demod', [status(thm)], ['18', '19'])).
% 1.18/1.44  thf('21', plain,
% 1.18/1.44      ((v2_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('22', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('23', plain,
% 1.18/1.44      ((v2_waybel_0 @ sk_B_2 @ 
% 1.18/1.44        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.18/1.44      inference('demod', [status(thm)], ['21', '22'])).
% 1.18/1.44  thf('24', plain,
% 1.18/1.44      ((v1_subset_1 @ sk_B_2 @ 
% 1.18/1.44        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('25', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('26', plain,
% 1.18/1.44      ((v1_subset_1 @ sk_B_2 @ 
% 1.18/1.44        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 1.18/1.44      inference('demod', [status(thm)], ['24', '25'])).
% 1.18/1.44  thf('27', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44          | (v2_struct_0 @ X0)
% 1.18/1.44          | ~ (l1_struct_0 @ X0)
% 1.18/1.44          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.18/1.44               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.18/1.44      inference('demod', [status(thm)], ['17', '20', '23', '26'])).
% 1.18/1.44  thf('28', plain,
% 1.18/1.44      ((~ (l1_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44        | ~ (l1_struct_0 @ sk_A)
% 1.18/1.44        | (v2_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['7', '27'])).
% 1.18/1.44  thf('29', plain,
% 1.18/1.44      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | (v2_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44        | ~ (l1_struct_0 @ sk_A))),
% 1.18/1.44      inference('simplify', [status(thm)], ['28'])).
% 1.18/1.44  thf('30', plain,
% 1.18/1.44      ((~ (l1_pre_topc @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44        | (v2_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['6', '29'])).
% 1.18/1.44  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('32', plain,
% 1.18/1.44      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44        | (v2_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.44      inference('demod', [status(thm)], ['30', '31'])).
% 1.18/1.44  thf('33', plain,
% 1.18/1.44      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.18/1.44  thf('34', plain,
% 1.18/1.44      (![X14 : $i]:
% 1.18/1.44         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 1.18/1.44           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.18/1.44          | ~ (l1_struct_0 @ X14))),
% 1.18/1.44      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.18/1.44  thf('35', plain,
% 1.18/1.44      ((m1_subset_1 @ sk_B_2 @ 
% 1.18/1.44        (k1_zfmisc_1 @ 
% 1.18/1.44         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.18/1.44      inference('demod', [status(thm)], ['8', '9'])).
% 1.18/1.44  thf(fc4_yellow19, axiom,
% 1.18/1.44    (![A:$i,B:$i,C:$i]:
% 1.18/1.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 1.18/1.44         ( ~( v1_xboole_0 @ B ) ) & 
% 1.18/1.44         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.18/1.44         ( ~( v1_xboole_0 @ C ) ) & 
% 1.18/1.44         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 1.18/1.44         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 1.18/1.44         ( m1_subset_1 @
% 1.18/1.44           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 1.18/1.44       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 1.18/1.44         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 1.18/1.44         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 1.18/1.44         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 1.18/1.44  thf('36', plain,
% 1.18/1.44      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.18/1.44         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.18/1.44          | (v1_xboole_0 @ X21)
% 1.18/1.44          | ~ (l1_struct_0 @ X22)
% 1.18/1.44          | (v2_struct_0 @ X22)
% 1.18/1.44          | (v1_xboole_0 @ X23)
% 1.18/1.44          | ~ (v2_waybel_0 @ X23 @ (k3_yellow_1 @ X21))
% 1.18/1.44          | ~ (v13_waybel_0 @ X23 @ (k3_yellow_1 @ X21))
% 1.18/1.44          | ~ (m1_subset_1 @ X23 @ 
% 1.18/1.44               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X21))))
% 1.18/1.44          | (v4_orders_2 @ (k3_yellow19 @ X22 @ X21 @ X23)))),
% 1.18/1.44      inference('cnf', [status(esa)], [fc4_yellow19])).
% 1.18/1.44  thf('37', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('38', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('39', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('40', plain,
% 1.18/1.44      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.18/1.44         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.18/1.44          | (v1_xboole_0 @ X21)
% 1.18/1.44          | ~ (l1_struct_0 @ X22)
% 1.18/1.44          | (v2_struct_0 @ X22)
% 1.18/1.44          | (v1_xboole_0 @ X23)
% 1.18/1.44          | ~ (v2_waybel_0 @ X23 @ (k3_lattice3 @ (k1_lattice3 @ X21)))
% 1.18/1.44          | ~ (v13_waybel_0 @ X23 @ (k3_lattice3 @ (k1_lattice3 @ X21)))
% 1.18/1.44          | ~ (m1_subset_1 @ X23 @ 
% 1.18/1.44               (k1_zfmisc_1 @ 
% 1.18/1.44                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X21)))))
% 1.18/1.44          | (v4_orders_2 @ (k3_yellow19 @ X22 @ X21 @ X23)))),
% 1.18/1.44      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 1.18/1.44  thf('41', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 1.18/1.44               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.18/1.44          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 1.18/1.44               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.18/1.44          | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44          | (v2_struct_0 @ X0)
% 1.18/1.44          | ~ (l1_struct_0 @ X0)
% 1.18/1.44          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.18/1.44               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.18/1.44      inference('sup-', [status(thm)], ['35', '40'])).
% 1.18/1.44  thf('42', plain,
% 1.18/1.44      ((v13_waybel_0 @ sk_B_2 @ 
% 1.18/1.44        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.18/1.44      inference('demod', [status(thm)], ['18', '19'])).
% 1.18/1.44  thf('43', plain,
% 1.18/1.44      ((v2_waybel_0 @ sk_B_2 @ 
% 1.18/1.44        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.18/1.44      inference('demod', [status(thm)], ['21', '22'])).
% 1.18/1.44  thf('44', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44          | (v2_struct_0 @ X0)
% 1.18/1.44          | ~ (l1_struct_0 @ X0)
% 1.18/1.44          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.18/1.44               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.18/1.44      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.18/1.44  thf('45', plain,
% 1.18/1.44      ((~ (l1_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44        | ~ (l1_struct_0 @ sk_A)
% 1.18/1.44        | (v2_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['34', '44'])).
% 1.18/1.44  thf('46', plain,
% 1.18/1.44      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | (v2_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44        | ~ (l1_struct_0 @ sk_A))),
% 1.18/1.44      inference('simplify', [status(thm)], ['45'])).
% 1.18/1.44  thf('47', plain,
% 1.18/1.44      ((~ (l1_pre_topc @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44        | (v2_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['33', '46'])).
% 1.18/1.44  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('49', plain,
% 1.18/1.44      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44        | (v2_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.44      inference('demod', [status(thm)], ['47', '48'])).
% 1.18/1.44  thf('50', plain,
% 1.18/1.44      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.18/1.44  thf('51', plain,
% 1.18/1.44      (![X14 : $i]:
% 1.18/1.44         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 1.18/1.44           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.18/1.44          | ~ (l1_struct_0 @ X14))),
% 1.18/1.44      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.18/1.44  thf('52', plain,
% 1.18/1.44      ((m1_subset_1 @ sk_B_2 @ 
% 1.18/1.44        (k1_zfmisc_1 @ 
% 1.18/1.44         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.18/1.44      inference('demod', [status(thm)], ['8', '9'])).
% 1.18/1.44  thf(dt_k3_yellow19, axiom,
% 1.18/1.44    (![A:$i,B:$i,C:$i]:
% 1.18/1.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 1.18/1.44         ( ~( v1_xboole_0 @ B ) ) & 
% 1.18/1.44         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.18/1.44         ( ~( v1_xboole_0 @ C ) ) & 
% 1.18/1.44         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 1.18/1.44         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 1.18/1.44         ( m1_subset_1 @
% 1.18/1.44           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 1.18/1.44       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 1.18/1.44         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 1.18/1.44         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 1.18/1.44  thf('53', plain,
% 1.18/1.44      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.18/1.44         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.18/1.44          | (v1_xboole_0 @ X18)
% 1.18/1.44          | ~ (l1_struct_0 @ X19)
% 1.18/1.44          | (v2_struct_0 @ X19)
% 1.18/1.44          | (v1_xboole_0 @ X20)
% 1.18/1.44          | ~ (v2_waybel_0 @ X20 @ (k3_yellow_1 @ X18))
% 1.18/1.44          | ~ (v13_waybel_0 @ X20 @ (k3_yellow_1 @ X18))
% 1.18/1.44          | ~ (m1_subset_1 @ X20 @ 
% 1.18/1.44               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X18))))
% 1.18/1.44          | (l1_waybel_0 @ (k3_yellow19 @ X19 @ X18 @ X20) @ X19))),
% 1.18/1.44      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 1.18/1.44  thf('54', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('55', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('56', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('57', plain,
% 1.18/1.44      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.18/1.44         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.18/1.44          | (v1_xboole_0 @ X18)
% 1.18/1.44          | ~ (l1_struct_0 @ X19)
% 1.18/1.44          | (v2_struct_0 @ X19)
% 1.18/1.44          | (v1_xboole_0 @ X20)
% 1.18/1.44          | ~ (v2_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 1.18/1.44          | ~ (v13_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 1.18/1.44          | ~ (m1_subset_1 @ X20 @ 
% 1.18/1.44               (k1_zfmisc_1 @ 
% 1.18/1.44                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18)))))
% 1.18/1.44          | (l1_waybel_0 @ (k3_yellow19 @ X19 @ X18 @ X20) @ X19))),
% 1.18/1.44      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 1.18/1.44  thf('58', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2) @ 
% 1.18/1.44           X0)
% 1.18/1.44          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 1.18/1.44               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.18/1.44          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 1.18/1.44               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.18/1.44          | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44          | (v2_struct_0 @ X0)
% 1.18/1.44          | ~ (l1_struct_0 @ X0)
% 1.18/1.44          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.18/1.44               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.18/1.44      inference('sup-', [status(thm)], ['52', '57'])).
% 1.18/1.44  thf('59', plain,
% 1.18/1.44      ((v13_waybel_0 @ sk_B_2 @ 
% 1.18/1.44        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.18/1.44      inference('demod', [status(thm)], ['18', '19'])).
% 1.18/1.44  thf('60', plain,
% 1.18/1.44      ((v2_waybel_0 @ sk_B_2 @ 
% 1.18/1.44        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.18/1.44      inference('demod', [status(thm)], ['21', '22'])).
% 1.18/1.44  thf('61', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2) @ 
% 1.18/1.44           X0)
% 1.18/1.44          | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44          | (v2_struct_0 @ X0)
% 1.18/1.44          | ~ (l1_struct_0 @ X0)
% 1.18/1.44          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.18/1.44               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.18/1.44      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.18/1.44  thf('62', plain,
% 1.18/1.44      ((~ (l1_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44        | ~ (l1_struct_0 @ sk_A)
% 1.18/1.44        | (v2_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | (l1_waybel_0 @ 
% 1.18/1.44           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A))),
% 1.18/1.44      inference('sup-', [status(thm)], ['51', '61'])).
% 1.18/1.44  thf('63', plain,
% 1.18/1.44      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ 
% 1.18/1.44         sk_A)
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | (v2_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44        | ~ (l1_struct_0 @ sk_A))),
% 1.18/1.44      inference('simplify', [status(thm)], ['62'])).
% 1.18/1.44  thf('64', plain,
% 1.18/1.44      ((~ (l1_pre_topc @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44        | (v2_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | (l1_waybel_0 @ 
% 1.18/1.44           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A))),
% 1.18/1.44      inference('sup-', [status(thm)], ['50', '63'])).
% 1.18/1.44  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('66', plain,
% 1.18/1.44      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44        | (v2_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | (l1_waybel_0 @ 
% 1.18/1.44           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A))),
% 1.18/1.44      inference('demod', [status(thm)], ['64', '65'])).
% 1.18/1.44  thf('67', plain,
% 1.18/1.44      (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)
% 1.18/1.44        | (r3_waybel_9 @ sk_A @ 
% 1.18/1.44           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('68', plain,
% 1.18/1.44      (((r3_waybel_9 @ sk_A @ 
% 1.18/1.44         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1))
% 1.18/1.44         <= (((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('split', [status(esa)], ['67'])).
% 1.18/1.44  thf('69', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf(t12_yellow19, axiom,
% 1.18/1.44    (![A:$i]:
% 1.18/1.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.18/1.44       ( ![B:$i]:
% 1.18/1.44         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 1.18/1.44             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 1.18/1.44           ( ![C:$i]:
% 1.18/1.44             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.18/1.44               ( ( r3_waybel_9 @ A @ B @ C ) <=>
% 1.18/1.44                 ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 1.18/1.44  thf('70', plain,
% 1.18/1.44      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.18/1.44         ((v2_struct_0 @ X27)
% 1.18/1.44          | ~ (v4_orders_2 @ X27)
% 1.18/1.44          | ~ (v7_waybel_0 @ X27)
% 1.18/1.44          | ~ (l1_waybel_0 @ X27 @ X28)
% 1.18/1.44          | ~ (r3_waybel_9 @ X28 @ X27 @ X29)
% 1.18/1.44          | (r1_waybel_7 @ X28 @ (k2_yellow19 @ X28 @ X27) @ X29)
% 1.18/1.44          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 1.18/1.44          | ~ (l1_pre_topc @ X28)
% 1.18/1.44          | ~ (v2_pre_topc @ X28)
% 1.18/1.44          | (v2_struct_0 @ X28))),
% 1.18/1.44      inference('cnf', [status(esa)], [t12_yellow19])).
% 1.18/1.44  thf('71', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((v2_struct_0 @ sk_A)
% 1.18/1.44          | ~ (v2_pre_topc @ sk_A)
% 1.18/1.44          | ~ (l1_pre_topc @ sk_A)
% 1.18/1.44          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C_1)
% 1.18/1.44          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C_1)
% 1.18/1.44          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 1.18/1.44          | ~ (v7_waybel_0 @ X0)
% 1.18/1.44          | ~ (v4_orders_2 @ X0)
% 1.18/1.44          | (v2_struct_0 @ X0))),
% 1.18/1.44      inference('sup-', [status(thm)], ['69', '70'])).
% 1.18/1.44  thf('72', plain, ((v2_pre_topc @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('74', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((v2_struct_0 @ sk_A)
% 1.18/1.44          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C_1)
% 1.18/1.44          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C_1)
% 1.18/1.44          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 1.18/1.44          | ~ (v7_waybel_0 @ X0)
% 1.18/1.44          | ~ (v4_orders_2 @ X0)
% 1.18/1.44          | (v2_struct_0 @ X0))),
% 1.18/1.44      inference('demod', [status(thm)], ['71', '72', '73'])).
% 1.18/1.44  thf('75', plain,
% 1.18/1.44      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44         | ~ (v4_orders_2 @ 
% 1.18/1.44              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44         | ~ (v7_waybel_0 @ 
% 1.18/1.44              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44         | ~ (l1_waybel_0 @ 
% 1.18/1.44              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 1.18/1.44         | (r1_waybel_7 @ sk_A @ 
% 1.18/1.44            (k2_yellow19 @ sk_A @ 
% 1.18/1.44             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)) @ 
% 1.18/1.44            sk_C_1)
% 1.18/1.44         | (v2_struct_0 @ sk_A)))
% 1.18/1.44         <= (((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['68', '74'])).
% 1.18/1.44  thf('76', plain,
% 1.18/1.44      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.18/1.44  thf('77', plain,
% 1.18/1.44      ((m1_subset_1 @ sk_B_2 @ 
% 1.18/1.44        (k1_zfmisc_1 @ 
% 1.18/1.44         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.18/1.44      inference('demod', [status(thm)], ['8', '9'])).
% 1.18/1.44  thf(t15_yellow19, axiom,
% 1.18/1.44    (![A:$i]:
% 1.18/1.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.18/1.44       ( ![B:$i]:
% 1.18/1.44         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.18/1.44             ( v1_subset_1 @
% 1.18/1.44               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 1.18/1.44             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.18/1.44             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.18/1.44             ( m1_subset_1 @
% 1.18/1.44               B @ 
% 1.18/1.44               ( k1_zfmisc_1 @
% 1.18/1.44                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 1.18/1.44           ( ( B ) =
% 1.18/1.44             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 1.18/1.44  thf('78', plain,
% 1.18/1.44      (![X30 : $i, X31 : $i]:
% 1.18/1.44         ((v1_xboole_0 @ X30)
% 1.18/1.44          | ~ (v1_subset_1 @ X30 @ 
% 1.18/1.44               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X31))))
% 1.18/1.44          | ~ (v2_waybel_0 @ X30 @ (k3_yellow_1 @ (k2_struct_0 @ X31)))
% 1.18/1.44          | ~ (v13_waybel_0 @ X30 @ (k3_yellow_1 @ (k2_struct_0 @ X31)))
% 1.18/1.44          | ~ (m1_subset_1 @ X30 @ 
% 1.18/1.44               (k1_zfmisc_1 @ 
% 1.18/1.44                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X31)))))
% 1.18/1.44          | ((X30)
% 1.18/1.44              = (k2_yellow19 @ X31 @ 
% 1.18/1.44                 (k3_yellow19 @ X31 @ (k2_struct_0 @ X31) @ X30)))
% 1.18/1.44          | ~ (l1_struct_0 @ X31)
% 1.18/1.44          | (v2_struct_0 @ X31))),
% 1.18/1.44      inference('cnf', [status(esa)], [t15_yellow19])).
% 1.18/1.44  thf('79', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('80', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('81', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('82', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('83', plain,
% 1.18/1.44      (![X30 : $i, X31 : $i]:
% 1.18/1.44         ((v1_xboole_0 @ X30)
% 1.18/1.44          | ~ (v1_subset_1 @ X30 @ 
% 1.18/1.44               (u1_struct_0 @ 
% 1.18/1.44                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X31)))))
% 1.18/1.44          | ~ (v2_waybel_0 @ X30 @ 
% 1.18/1.44               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X31))))
% 1.18/1.44          | ~ (v13_waybel_0 @ X30 @ 
% 1.18/1.44               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X31))))
% 1.18/1.44          | ~ (m1_subset_1 @ X30 @ 
% 1.18/1.44               (k1_zfmisc_1 @ 
% 1.18/1.44                (u1_struct_0 @ 
% 1.18/1.44                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X31))))))
% 1.18/1.44          | ((X30)
% 1.18/1.44              = (k2_yellow19 @ X31 @ 
% 1.18/1.44                 (k3_yellow19 @ X31 @ (k2_struct_0 @ X31) @ X30)))
% 1.18/1.44          | ~ (l1_struct_0 @ X31)
% 1.18/1.44          | (v2_struct_0 @ X31))),
% 1.18/1.44      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 1.18/1.44  thf('84', plain,
% 1.18/1.44      (((v2_struct_0 @ sk_A)
% 1.18/1.44        | ~ (l1_struct_0 @ sk_A)
% 1.18/1.44        | ((sk_B_2)
% 1.18/1.44            = (k2_yellow19 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 1.18/1.44        | ~ (v13_waybel_0 @ sk_B_2 @ 
% 1.18/1.44             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.18/1.44        | ~ (v2_waybel_0 @ sk_B_2 @ 
% 1.18/1.44             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.18/1.44        | ~ (v1_subset_1 @ sk_B_2 @ 
% 1.18/1.44             (u1_struct_0 @ 
% 1.18/1.44              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2))),
% 1.18/1.44      inference('sup-', [status(thm)], ['77', '83'])).
% 1.18/1.44  thf('85', plain,
% 1.18/1.44      ((v13_waybel_0 @ sk_B_2 @ 
% 1.18/1.44        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.18/1.44      inference('demod', [status(thm)], ['18', '19'])).
% 1.18/1.44  thf('86', plain,
% 1.18/1.44      ((v2_waybel_0 @ sk_B_2 @ 
% 1.18/1.44        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.18/1.44      inference('demod', [status(thm)], ['21', '22'])).
% 1.18/1.44  thf('87', plain,
% 1.18/1.44      ((v1_subset_1 @ sk_B_2 @ 
% 1.18/1.44        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 1.18/1.44      inference('demod', [status(thm)], ['24', '25'])).
% 1.18/1.44  thf('88', plain,
% 1.18/1.44      (((v2_struct_0 @ sk_A)
% 1.18/1.44        | ~ (l1_struct_0 @ sk_A)
% 1.18/1.44        | ((sk_B_2)
% 1.18/1.44            = (k2_yellow19 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2))),
% 1.18/1.44      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 1.18/1.44  thf('89', plain,
% 1.18/1.44      ((~ (l1_pre_topc @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | ((sk_B_2)
% 1.18/1.44            = (k2_yellow19 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 1.18/1.44        | (v2_struct_0 @ sk_A))),
% 1.18/1.44      inference('sup-', [status(thm)], ['76', '88'])).
% 1.18/1.44  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('91', plain,
% 1.18/1.44      (((v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | ((sk_B_2)
% 1.18/1.44            = (k2_yellow19 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 1.18/1.44        | (v2_struct_0 @ sk_A))),
% 1.18/1.44      inference('demod', [status(thm)], ['89', '90'])).
% 1.18/1.44  thf('92', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('93', plain,
% 1.18/1.44      (((v2_struct_0 @ sk_A)
% 1.18/1.44        | ((sk_B_2)
% 1.18/1.44            = (k2_yellow19 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))),
% 1.18/1.44      inference('clc', [status(thm)], ['91', '92'])).
% 1.18/1.44  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('95', plain,
% 1.18/1.44      (((sk_B_2)
% 1.18/1.44         = (k2_yellow19 @ sk_A @ 
% 1.18/1.44            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.44      inference('clc', [status(thm)], ['93', '94'])).
% 1.18/1.44  thf('96', plain,
% 1.18/1.44      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44         | ~ (v4_orders_2 @ 
% 1.18/1.44              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44         | ~ (v7_waybel_0 @ 
% 1.18/1.44              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44         | ~ (l1_waybel_0 @ 
% 1.18/1.44              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 1.18/1.44         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)
% 1.18/1.44         | (v2_struct_0 @ sk_A)))
% 1.18/1.44         <= (((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('demod', [status(thm)], ['75', '95'])).
% 1.18/1.44  thf('97', plain,
% 1.18/1.44      ((((v1_xboole_0 @ sk_B_2)
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)
% 1.18/1.44         | ~ (v7_waybel_0 @ 
% 1.18/1.44              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44         | ~ (v4_orders_2 @ 
% 1.18/1.44              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))
% 1.18/1.44         <= (((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['66', '96'])).
% 1.18/1.44  thf('98', plain,
% 1.18/1.44      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44         | ~ (v4_orders_2 @ 
% 1.18/1.44              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44         | ~ (v7_waybel_0 @ 
% 1.18/1.44              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ sk_B_2)))
% 1.18/1.44         <= (((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('simplify', [status(thm)], ['97'])).
% 1.18/1.44  thf('99', plain,
% 1.18/1.44      ((((v1_xboole_0 @ sk_B_2)
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)
% 1.18/1.44         | ~ (v7_waybel_0 @ 
% 1.18/1.44              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))
% 1.18/1.44         <= (((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['49', '98'])).
% 1.18/1.44  thf('100', plain,
% 1.18/1.44      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44         | ~ (v7_waybel_0 @ 
% 1.18/1.44              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ sk_B_2)))
% 1.18/1.44         <= (((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('simplify', [status(thm)], ['99'])).
% 1.18/1.44  thf('101', plain,
% 1.18/1.44      ((((v1_xboole_0 @ sk_B_2)
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)
% 1.18/1.44         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))
% 1.18/1.44         <= (((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['32', '100'])).
% 1.18/1.44  thf('102', plain,
% 1.18/1.44      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ sk_B_2)))
% 1.18/1.44         <= (((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('simplify', [status(thm)], ['101'])).
% 1.18/1.44  thf('103', plain,
% 1.18/1.44      (![X14 : $i]:
% 1.18/1.44         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 1.18/1.44           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.18/1.44          | ~ (l1_struct_0 @ X14))),
% 1.18/1.44      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.18/1.44  thf('104', plain,
% 1.18/1.44      ((m1_subset_1 @ sk_B_2 @ 
% 1.18/1.44        (k1_zfmisc_1 @ 
% 1.18/1.44         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.18/1.44      inference('demod', [status(thm)], ['8', '9'])).
% 1.18/1.44  thf('105', plain,
% 1.18/1.44      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.18/1.44         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.18/1.44          | (v1_xboole_0 @ X18)
% 1.18/1.44          | ~ (l1_struct_0 @ X19)
% 1.18/1.44          | (v2_struct_0 @ X19)
% 1.18/1.44          | (v1_xboole_0 @ X20)
% 1.18/1.44          | ~ (v2_waybel_0 @ X20 @ (k3_yellow_1 @ X18))
% 1.18/1.44          | ~ (v13_waybel_0 @ X20 @ (k3_yellow_1 @ X18))
% 1.18/1.44          | ~ (m1_subset_1 @ X20 @ 
% 1.18/1.44               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X18))))
% 1.18/1.44          | ~ (v2_struct_0 @ (k3_yellow19 @ X19 @ X18 @ X20)))),
% 1.18/1.44      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 1.18/1.44  thf('106', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('107', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('108', plain,
% 1.18/1.44      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.18/1.44  thf('109', plain,
% 1.18/1.44      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.18/1.44         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.18/1.44          | (v1_xboole_0 @ X18)
% 1.18/1.44          | ~ (l1_struct_0 @ X19)
% 1.18/1.44          | (v2_struct_0 @ X19)
% 1.18/1.44          | (v1_xboole_0 @ X20)
% 1.18/1.44          | ~ (v2_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 1.18/1.44          | ~ (v13_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 1.18/1.44          | ~ (m1_subset_1 @ X20 @ 
% 1.18/1.44               (k1_zfmisc_1 @ 
% 1.18/1.44                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18)))))
% 1.18/1.44          | ~ (v2_struct_0 @ (k3_yellow19 @ X19 @ X18 @ X20)))),
% 1.18/1.44      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 1.18/1.44  thf('110', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 1.18/1.44               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.18/1.44          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 1.18/1.44               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.18/1.44          | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44          | (v2_struct_0 @ X0)
% 1.18/1.44          | ~ (l1_struct_0 @ X0)
% 1.18/1.44          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.18/1.44               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.18/1.44      inference('sup-', [status(thm)], ['104', '109'])).
% 1.18/1.44  thf('111', plain,
% 1.18/1.44      ((v13_waybel_0 @ sk_B_2 @ 
% 1.18/1.44        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.18/1.44      inference('demod', [status(thm)], ['18', '19'])).
% 1.18/1.44  thf('112', plain,
% 1.18/1.44      ((v2_waybel_0 @ sk_B_2 @ 
% 1.18/1.44        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.18/1.44      inference('demod', [status(thm)], ['21', '22'])).
% 1.18/1.44  thf('113', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44          | (v2_struct_0 @ X0)
% 1.18/1.44          | ~ (l1_struct_0 @ X0)
% 1.18/1.44          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.18/1.44               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.18/1.44      inference('demod', [status(thm)], ['110', '111', '112'])).
% 1.18/1.44  thf('114', plain,
% 1.18/1.44      ((~ (l1_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44        | ~ (l1_struct_0 @ sk_A)
% 1.18/1.44        | (v2_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['103', '113'])).
% 1.18/1.44  thf('115', plain,
% 1.18/1.44      ((~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | (v2_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44        | ~ (l1_struct_0 @ sk_A))),
% 1.18/1.44      inference('simplify', [status(thm)], ['114'])).
% 1.18/1.44  thf('116', plain,
% 1.18/1.44      ((((v1_xboole_0 @ sk_B_2)
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)
% 1.18/1.44         | ~ (l1_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ sk_B_2)))
% 1.18/1.44         <= (((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['102', '115'])).
% 1.18/1.44  thf('117', plain,
% 1.18/1.44      (((~ (l1_struct_0 @ sk_A)
% 1.18/1.44         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ sk_B_2)))
% 1.18/1.44         <= (((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('simplify', [status(thm)], ['116'])).
% 1.18/1.44  thf('118', plain,
% 1.18/1.44      (((~ (l1_pre_topc @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))
% 1.18/1.44         <= (((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['5', '117'])).
% 1.18/1.44  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('120', plain,
% 1.18/1.44      ((((v1_xboole_0 @ sk_B_2)
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))
% 1.18/1.44         <= (((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('demod', [status(thm)], ['118', '119'])).
% 1.18/1.44  thf('121', plain,
% 1.18/1.44      ((~ (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1))
% 1.18/1.44         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('split', [status(esa)], ['0'])).
% 1.18/1.44  thf('122', plain,
% 1.18/1.44      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ sk_B_2)))
% 1.18/1.44         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) & 
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['120', '121'])).
% 1.18/1.44  thf('123', plain, (~ (v2_struct_0 @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('124', plain,
% 1.18/1.44      ((((v1_xboole_0 @ sk_B_2) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 1.18/1.44         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) & 
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('clc', [status(thm)], ['122', '123'])).
% 1.18/1.44  thf('125', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('126', plain,
% 1.18/1.44      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 1.18/1.44         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) & 
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('clc', [status(thm)], ['124', '125'])).
% 1.18/1.44  thf('127', plain,
% 1.18/1.44      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 1.18/1.44         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) & 
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('sup+', [status(thm)], ['4', '126'])).
% 1.18/1.44  thf('128', plain,
% 1.18/1.44      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.18/1.44         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) & 
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['3', '127'])).
% 1.18/1.44  thf('129', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('130', plain,
% 1.18/1.44      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 1.18/1.44         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) & 
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('demod', [status(thm)], ['128', '129'])).
% 1.18/1.44  thf(d1_xboole_0, axiom,
% 1.18/1.44    (![A:$i]:
% 1.18/1.44     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.18/1.44  thf('131', plain,
% 1.18/1.44      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.18/1.44      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.18/1.44  thf(rc20_struct_0, axiom,
% 1.18/1.44    (![A:$i]:
% 1.18/1.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.18/1.44       ( ?[B:$i]:
% 1.18/1.44         ( ( v1_zfmisc_1 @ B ) & ( ~( v1_xboole_0 @ B ) ) & 
% 1.18/1.44           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.18/1.44  thf('132', plain,
% 1.18/1.44      (![X16 : $i]:
% 1.18/1.44         ((m1_subset_1 @ (sk_B_1 @ X16) @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.18/1.44          | ~ (l1_struct_0 @ X16)
% 1.18/1.44          | (v2_struct_0 @ X16))),
% 1.18/1.44      inference('cnf', [status(esa)], [rc20_struct_0])).
% 1.18/1.44  thf(t3_subset, axiom,
% 1.18/1.44    (![A:$i,B:$i]:
% 1.18/1.44     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.18/1.44  thf('133', plain,
% 1.18/1.44      (![X10 : $i, X11 : $i]:
% 1.18/1.44         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.18/1.44      inference('cnf', [status(esa)], [t3_subset])).
% 1.18/1.44  thf('134', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((v2_struct_0 @ X0)
% 1.18/1.44          | ~ (l1_struct_0 @ X0)
% 1.18/1.44          | (r1_tarski @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['132', '133'])).
% 1.18/1.44  thf(d3_tarski, axiom,
% 1.18/1.44    (![A:$i,B:$i]:
% 1.18/1.44     ( ( r1_tarski @ A @ B ) <=>
% 1.18/1.44       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.18/1.44  thf('135', plain,
% 1.18/1.44      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.18/1.44         (~ (r2_hidden @ X3 @ X4)
% 1.18/1.44          | (r2_hidden @ X3 @ X5)
% 1.18/1.44          | ~ (r1_tarski @ X4 @ X5))),
% 1.18/1.44      inference('cnf', [status(esa)], [d3_tarski])).
% 1.18/1.44  thf('136', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]:
% 1.18/1.44         (~ (l1_struct_0 @ X0)
% 1.18/1.44          | (v2_struct_0 @ X0)
% 1.18/1.44          | (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 1.18/1.44          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['134', '135'])).
% 1.18/1.44  thf('137', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 1.18/1.44          | (r2_hidden @ (sk_B @ (sk_B_1 @ X0)) @ (u1_struct_0 @ X0))
% 1.18/1.44          | (v2_struct_0 @ X0)
% 1.18/1.44          | ~ (l1_struct_0 @ X0))),
% 1.18/1.44      inference('sup-', [status(thm)], ['131', '136'])).
% 1.18/1.44  thf('138', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.18/1.44      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.18/1.44  thf('139', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         (~ (l1_struct_0 @ X0)
% 1.18/1.44          | (v2_struct_0 @ X0)
% 1.18/1.44          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 1.18/1.44          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['137', '138'])).
% 1.18/1.44  thf('140', plain,
% 1.18/1.44      ((((v1_xboole_0 @ (sk_B_1 @ sk_A))
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | ~ (l1_struct_0 @ sk_A)))
% 1.18/1.44         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) & 
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['130', '139'])).
% 1.18/1.44  thf('141', plain,
% 1.18/1.44      (![X16 : $i]:
% 1.18/1.44         (~ (v1_xboole_0 @ (sk_B_1 @ X16))
% 1.18/1.44          | ~ (l1_struct_0 @ X16)
% 1.18/1.44          | (v2_struct_0 @ X16))),
% 1.18/1.44      inference('cnf', [status(esa)], [rc20_struct_0])).
% 1.18/1.44  thf('142', plain,
% 1.18/1.44      (((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A)))
% 1.18/1.44         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) & 
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('clc', [status(thm)], ['140', '141'])).
% 1.18/1.44  thf('143', plain, (~ (v2_struct_0 @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('144', plain,
% 1.18/1.44      ((~ (l1_struct_0 @ sk_A))
% 1.18/1.44         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) & 
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('clc', [status(thm)], ['142', '143'])).
% 1.18/1.44  thf('145', plain,
% 1.18/1.44      ((~ (l1_pre_topc @ sk_A))
% 1.18/1.44         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) & 
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['2', '144'])).
% 1.18/1.44  thf('146', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('147', plain,
% 1.18/1.44      (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) | 
% 1.18/1.44       ~
% 1.18/1.44       ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1))),
% 1.18/1.44      inference('demod', [status(thm)], ['145', '146'])).
% 1.18/1.44  thf('148', plain,
% 1.18/1.44      (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) | 
% 1.18/1.44       ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1))),
% 1.18/1.44      inference('split', [status(esa)], ['67'])).
% 1.18/1.44  thf('149', plain,
% 1.18/1.44      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.18/1.44  thf('150', plain,
% 1.18/1.44      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.18/1.44  thf('151', plain,
% 1.18/1.44      (![X13 : $i]:
% 1.18/1.44         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 1.18/1.44      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.44  thf('152', plain,
% 1.18/1.44      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.18/1.44  thf('153', plain,
% 1.18/1.44      (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1))
% 1.18/1.44         <= (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('split', [status(esa)], ['67'])).
% 1.18/1.44  thf('154', plain,
% 1.18/1.44      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44        | (v2_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.44      inference('demod', [status(thm)], ['47', '48'])).
% 1.18/1.44  thf('155', plain,
% 1.18/1.44      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44        | (v2_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.44      inference('demod', [status(thm)], ['30', '31'])).
% 1.18/1.44  thf('156', plain,
% 1.18/1.44      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44        | (v2_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | (l1_waybel_0 @ 
% 1.18/1.44           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A))),
% 1.18/1.44      inference('demod', [status(thm)], ['64', '65'])).
% 1.18/1.44  thf('157', plain,
% 1.18/1.44      (((sk_B_2)
% 1.18/1.44         = (k2_yellow19 @ sk_A @ 
% 1.18/1.44            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.44      inference('clc', [status(thm)], ['93', '94'])).
% 1.18/1.44  thf('158', plain,
% 1.18/1.44      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.18/1.44         ((v2_struct_0 @ X27)
% 1.18/1.44          | ~ (v4_orders_2 @ X27)
% 1.18/1.44          | ~ (v7_waybel_0 @ X27)
% 1.18/1.44          | ~ (l1_waybel_0 @ X27 @ X28)
% 1.18/1.44          | ~ (r1_waybel_7 @ X28 @ (k2_yellow19 @ X28 @ X27) @ X29)
% 1.18/1.44          | (r3_waybel_9 @ X28 @ X27 @ X29)
% 1.18/1.44          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 1.18/1.44          | ~ (l1_pre_topc @ X28)
% 1.18/1.44          | ~ (v2_pre_topc @ X28)
% 1.18/1.44          | (v2_struct_0 @ X28))),
% 1.18/1.44      inference('cnf', [status(esa)], [t12_yellow19])).
% 1.18/1.44  thf('159', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         (~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 1.18/1.44          | (v2_struct_0 @ sk_A)
% 1.18/1.44          | ~ (v2_pre_topc @ sk_A)
% 1.18/1.44          | ~ (l1_pre_topc @ sk_A)
% 1.18/1.44          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.44          | (r3_waybel_9 @ sk_A @ 
% 1.18/1.44             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 1.18/1.44          | ~ (l1_waybel_0 @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 1.18/1.44          | ~ (v7_waybel_0 @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | ~ (v4_orders_2 @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['157', '158'])).
% 1.18/1.44  thf('160', plain, ((v2_pre_topc @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('161', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('162', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         (~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 1.18/1.44          | (v2_struct_0 @ sk_A)
% 1.18/1.44          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.44          | (r3_waybel_9 @ sk_A @ 
% 1.18/1.44             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 1.18/1.44          | ~ (l1_waybel_0 @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 1.18/1.44          | ~ (v7_waybel_0 @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | ~ (v4_orders_2 @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.44      inference('demod', [status(thm)], ['159', '160', '161'])).
% 1.18/1.44  thf('163', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((v1_xboole_0 @ sk_B_2)
% 1.18/1.44          | (v2_struct_0 @ sk_A)
% 1.18/1.44          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | ~ (v4_orders_2 @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | ~ (v7_waybel_0 @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | (r3_waybel_9 @ sk_A @ 
% 1.18/1.44             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 1.18/1.44          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.44          | (v2_struct_0 @ sk_A)
% 1.18/1.44          | ~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0))),
% 1.18/1.44      inference('sup-', [status(thm)], ['156', '162'])).
% 1.18/1.44  thf('164', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         (~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 1.18/1.44          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.44          | (r3_waybel_9 @ sk_A @ 
% 1.18/1.44             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 1.18/1.44          | ~ (v7_waybel_0 @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | ~ (v4_orders_2 @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44          | (v2_struct_0 @ sk_A)
% 1.18/1.44          | (v1_xboole_0 @ sk_B_2))),
% 1.18/1.44      inference('simplify', [status(thm)], ['163'])).
% 1.18/1.44  thf('165', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((v1_xboole_0 @ sk_B_2)
% 1.18/1.44          | (v2_struct_0 @ sk_A)
% 1.18/1.44          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44          | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44          | (v2_struct_0 @ sk_A)
% 1.18/1.44          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | ~ (v4_orders_2 @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | (r3_waybel_9 @ sk_A @ 
% 1.18/1.44             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 1.18/1.44          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.44          | ~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0))),
% 1.18/1.44      inference('sup-', [status(thm)], ['155', '164'])).
% 1.18/1.44  thf('166', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         (~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 1.18/1.44          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.44          | (r3_waybel_9 @ sk_A @ 
% 1.18/1.44             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 1.18/1.44          | ~ (v4_orders_2 @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44          | (v2_struct_0 @ sk_A)
% 1.18/1.44          | (v1_xboole_0 @ sk_B_2))),
% 1.18/1.44      inference('simplify', [status(thm)], ['165'])).
% 1.18/1.44  thf('167', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((v1_xboole_0 @ sk_B_2)
% 1.18/1.44          | (v2_struct_0 @ sk_A)
% 1.18/1.44          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44          | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44          | (v2_struct_0 @ sk_A)
% 1.18/1.44          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | (r3_waybel_9 @ sk_A @ 
% 1.18/1.44             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 1.18/1.44          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.44          | ~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0))),
% 1.18/1.44      inference('sup-', [status(thm)], ['154', '166'])).
% 1.18/1.44  thf('168', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         (~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 1.18/1.44          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.44          | (r3_waybel_9 @ sk_A @ 
% 1.18/1.44             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 1.18/1.44          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44          | (v2_struct_0 @ sk_A)
% 1.18/1.44          | (v1_xboole_0 @ sk_B_2))),
% 1.18/1.44      inference('simplify', [status(thm)], ['167'])).
% 1.18/1.44  thf('169', plain,
% 1.18/1.44      ((((v1_xboole_0 @ sk_B_2)
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44         | (r3_waybel_9 @ sk_A @ 
% 1.18/1.44            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)
% 1.18/1.44         | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))))
% 1.18/1.44         <= (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['153', '168'])).
% 1.18/1.44  thf('170', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('171', plain,
% 1.18/1.44      ((((v1_xboole_0 @ sk_B_2)
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44         | (r3_waybel_9 @ sk_A @ 
% 1.18/1.44            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))
% 1.18/1.44         <= (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('demod', [status(thm)], ['169', '170'])).
% 1.18/1.44  thf('172', plain,
% 1.18/1.44      ((~ (r3_waybel_9 @ sk_A @ 
% 1.18/1.44           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 1.18/1.44      inference('split', [status(esa)], ['0'])).
% 1.18/1.44  thf('173', plain,
% 1.18/1.44      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ sk_B_2)))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 1.18/1.44             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['171', '172'])).
% 1.18/1.44  thf('174', plain,
% 1.18/1.44      ((~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 1.18/1.44        | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44        | (v2_struct_0 @ sk_A)
% 1.18/1.44        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44        | ~ (l1_struct_0 @ sk_A))),
% 1.18/1.44      inference('simplify', [status(thm)], ['114'])).
% 1.18/1.44  thf('175', plain,
% 1.18/1.44      ((((v1_xboole_0 @ sk_B_2)
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | ~ (l1_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ sk_B_2)))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 1.18/1.44             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['173', '174'])).
% 1.18/1.44  thf('176', plain,
% 1.18/1.44      (((~ (l1_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ sk_B_2)))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 1.18/1.44             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('simplify', [status(thm)], ['175'])).
% 1.18/1.44  thf('177', plain,
% 1.18/1.44      (((~ (l1_pre_topc @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ sk_B_2)
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 1.18/1.44             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['152', '176'])).
% 1.18/1.44  thf('178', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('179', plain,
% 1.18/1.44      ((((v1_xboole_0 @ sk_B_2)
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 1.18/1.44             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('demod', [status(thm)], ['177', '178'])).
% 1.18/1.44  thf('180', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('181', plain,
% 1.18/1.44      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 1.18/1.44             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('clc', [status(thm)], ['179', '180'])).
% 1.18/1.44  thf('182', plain, (~ (v2_struct_0 @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('183', plain,
% 1.18/1.44      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 1.18/1.44             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('clc', [status(thm)], ['181', '182'])).
% 1.18/1.44  thf('184', plain,
% 1.18/1.44      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 1.18/1.44             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('sup+', [status(thm)], ['151', '183'])).
% 1.18/1.44  thf('185', plain,
% 1.18/1.44      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 1.18/1.44             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['150', '184'])).
% 1.18/1.44  thf('186', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('187', plain,
% 1.18/1.44      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 1.18/1.44             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('demod', [status(thm)], ['185', '186'])).
% 1.18/1.44  thf('188', plain,
% 1.18/1.44      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.18/1.44  thf('189', plain,
% 1.18/1.44      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 1.18/1.44             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('demod', [status(thm)], ['185', '186'])).
% 1.18/1.44  thf('190', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((v2_struct_0 @ X0)
% 1.18/1.44          | ~ (l1_struct_0 @ X0)
% 1.18/1.44          | (r1_tarski @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['132', '133'])).
% 1.18/1.44  thf('191', plain,
% 1.18/1.44      (![X4 : $i, X6 : $i]:
% 1.18/1.44         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.18/1.44      inference('cnf', [status(esa)], [d3_tarski])).
% 1.18/1.44  thf('192', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.18/1.44      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.18/1.44  thf('193', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.18/1.44      inference('sup-', [status(thm)], ['191', '192'])).
% 1.18/1.44  thf(d10_xboole_0, axiom,
% 1.18/1.44    (![A:$i,B:$i]:
% 1.18/1.44     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.18/1.44  thf('194', plain,
% 1.18/1.44      (![X7 : $i, X9 : $i]:
% 1.18/1.44         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 1.18/1.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.18/1.44  thf('195', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]:
% 1.18/1.44         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['193', '194'])).
% 1.18/1.44  thf('196', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         (~ (l1_struct_0 @ X0)
% 1.18/1.44          | (v2_struct_0 @ X0)
% 1.18/1.44          | ((sk_B_1 @ X0) = (u1_struct_0 @ X0))
% 1.18/1.44          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['190', '195'])).
% 1.18/1.44  thf('197', plain,
% 1.18/1.44      (((((sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A))
% 1.18/1.44         | (v2_struct_0 @ sk_A)
% 1.18/1.44         | ~ (l1_struct_0 @ sk_A)))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 1.18/1.44             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['189', '196'])).
% 1.18/1.44  thf('198', plain, (~ (v2_struct_0 @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('199', plain,
% 1.18/1.44      (((~ (l1_struct_0 @ sk_A) | ((sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A))))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 1.18/1.44             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('clc', [status(thm)], ['197', '198'])).
% 1.18/1.44  thf('200', plain,
% 1.18/1.44      (((~ (l1_pre_topc @ sk_A) | ((sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A))))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 1.18/1.44             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['188', '199'])).
% 1.18/1.44  thf('201', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('202', plain,
% 1.18/1.44      ((((sk_B_1 @ sk_A) = (u1_struct_0 @ sk_A)))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 1.18/1.44             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('demod', [status(thm)], ['200', '201'])).
% 1.18/1.44  thf('203', plain,
% 1.18/1.44      (((v1_xboole_0 @ (sk_B_1 @ sk_A)))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 1.18/1.44             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('demod', [status(thm)], ['187', '202'])).
% 1.18/1.44  thf('204', plain,
% 1.18/1.44      (![X16 : $i]:
% 1.18/1.44         (~ (v1_xboole_0 @ (sk_B_1 @ X16))
% 1.18/1.44          | ~ (l1_struct_0 @ X16)
% 1.18/1.44          | (v2_struct_0 @ X16))),
% 1.18/1.44      inference('cnf', [status(esa)], [rc20_struct_0])).
% 1.18/1.44  thf('205', plain,
% 1.18/1.44      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 1.18/1.44             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['203', '204'])).
% 1.18/1.44  thf('206', plain, (~ (v2_struct_0 @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('207', plain,
% 1.18/1.44      ((~ (l1_struct_0 @ sk_A))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 1.18/1.44             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('clc', [status(thm)], ['205', '206'])).
% 1.18/1.44  thf('208', plain,
% 1.18/1.44      ((~ (l1_pre_topc @ sk_A))
% 1.18/1.44         <= (~
% 1.18/1.44             ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 1.18/1.44             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['149', '207'])).
% 1.18/1.44  thf('209', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf('210', plain,
% 1.18/1.44      (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) | 
% 1.18/1.44       ((r3_waybel_9 @ sk_A @ 
% 1.18/1.44         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1))),
% 1.18/1.44      inference('demod', [status(thm)], ['208', '209'])).
% 1.18/1.44  thf('211', plain, ($false),
% 1.18/1.44      inference('sat_resolution*', [status(thm)], ['1', '147', '148', '210'])).
% 1.18/1.44  
% 1.18/1.44  % SZS output end Refutation
% 1.18/1.44  
% 1.18/1.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
