%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EMarRUYmCk

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  254 ( 678 expanded)
%              Number of leaves         :   45 ( 227 expanded)
%              Depth                    :   33
%              Number of atoms          : 3360 (13100 expanded)
%              Number of equality atoms :   47 ( 186 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

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
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('6',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_xboole_0 @ X19 )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( v1_subset_1 @ X21 @ ( u1_struct_0 @ ( k3_yellow_1 @ X19 ) ) )
      | ~ ( v2_waybel_0 @ X21 @ ( k3_yellow_1 @ X19 ) )
      | ~ ( v13_waybel_0 @ X21 @ ( k3_yellow_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X19 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X20 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('9',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('10',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('11',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('12',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('13',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_xboole_0 @ X19 )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( v1_subset_1 @ X21 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) )
      | ~ ( v2_waybel_0 @ X21 @ ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) )
      | ~ ( v13_waybel_0 @ X21 @ ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X20 @ X19 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('17',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('20',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('23',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['14','17','20','23'])).

thf('25',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','24'])).

thf('26',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('31',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('32',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf('33',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_xboole_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( v2_waybel_0 @ X18 @ ( k3_yellow_1 @ X16 ) )
      | ~ ( v13_waybel_0 @ X18 @ ( k3_yellow_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X16 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X17 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('34',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('35',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('36',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('37',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_xboole_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( v2_waybel_0 @ X18 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) )
      | ~ ( v13_waybel_0 @ X18 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X17 @ X16 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('40',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['31','41'])).

thf('43',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['30','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('48',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('49',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf('50',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v2_waybel_0 @ X15 @ ( k3_yellow_1 @ X13 ) )
      | ~ ( v13_waybel_0 @ X15 @ ( k3_yellow_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X13 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X14 @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('51',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('52',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('53',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('54',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v2_waybel_0 @ X15 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) )
      | ~ ( v13_waybel_0 @ X15 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X14 @ X13 @ X15 ) @ X14 ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('57',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['48','58'])).

thf('60',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['47','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,(
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

thf('67',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v7_waybel_0 @ X22 )
      | ~ ( l1_waybel_0 @ X22 @ X23 )
      | ~ ( r3_waybel_9 @ X23 @ X22 @ X24 )
      | ( r1_waybel_7 @ X23 @ ( k2_yellow19 @ X23 @ X22 ) @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('68',plain,(
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
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['63','72'])).

thf('74',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['46','74'])).

thf('76',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['29','76'])).

thf('78',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('79',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf('80',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_subset_1 @ X25 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X26 ) ) ) )
      | ~ ( v2_waybel_0 @ X25 @ ( k3_yellow_1 @ ( k2_struct_0 @ X26 ) ) )
      | ~ ( v13_waybel_0 @ X25 @ ( k3_yellow_1 @ ( k2_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X26 ) ) ) ) )
      | ( X25
        = ( k2_yellow19 @ X26 @ ( k3_yellow19 @ X26 @ ( k2_struct_0 @ X26 ) @ X25 ) ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('81',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('82',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('83',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('84',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('85',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_subset_1 @ X25 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X26 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X25 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X26 ) ) ) )
      | ~ ( v13_waybel_0 @ X25 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X26 ) ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X26 ) ) ) ) ) )
      | ( X25
        = ( k2_yellow19 @ X26 @ ( k3_yellow19 @ X26 @ ( k2_struct_0 @ X26 ) @ X25 ) ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','85'])).

thf('87',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('88',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('89',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( sk_B_1
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['77','97'])).

thf('99',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('101',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('102',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v2_waybel_0 @ X15 @ ( k3_yellow_1 @ X13 ) )
      | ~ ( v13_waybel_0 @ X15 @ ( k3_yellow_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X13 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('103',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('104',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('105',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('106',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v2_waybel_0 @ X15 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) )
      | ~ ( v13_waybel_0 @ X15 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X14 @ X13 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['102','103','104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('109',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['100','110'])).

thf('112',plain,
    ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['99','112'])).

thf('114',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['2','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
   <= ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('119',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf(t27_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('124',plain,(
    ! [X9: $i] :
      ( ( ( k2_pre_topc @ X9 @ ( k2_struct_0 @ X9 ) )
        = ( k2_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_tops_1])).

thf('125',plain,(
    ! [X9: $i] :
      ( ( ( k2_pre_topc @ X9 @ ( k2_struct_0 @ X9 ) )
        = ( k2_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_tops_1])).

thf('126',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('127',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( ( k2_pre_topc @ X8 @ X7 )
       != ( k2_struct_0 @ X8 ) )
      | ( v1_tops_1 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
       != ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('134',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v1_tops_1 @ X11 @ X12 )
      | ( ( k2_pre_topc @ X12 @ X11 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['124','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('142',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('143',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['141','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['123','146'])).

thf('148',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X6 ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('154',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['64'])).

thf('161',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('162',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
   <= ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['64'])).

thf('163',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('164',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('165',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('166',plain,
    ( sk_B_1
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('167',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v7_waybel_0 @ X22 )
      | ~ ( l1_waybel_0 @ X22 @ X23 )
      | ~ ( r1_waybel_7 @ X23 @ ( k2_yellow19 @ X23 @ X22 ) @ X24 )
      | ( r3_waybel_9 @ X23 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['164','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['162','177'])).

thf('179',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('182',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['111'])).

thf('184',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['161','185'])).

thf('187',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['188','189'])).

thf('191',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('194',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X6 ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('201',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['201','202','203'])).

thf('205',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','159','160','206'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EMarRUYmCk
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 175 iterations in 0.124s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.55  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.21/0.55  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.55  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.21/0.55  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.55  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 0.21/0.55  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.21/0.55  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.21/0.55  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.21/0.55  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.21/0.55  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.55  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.21/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.55  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.21/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.55  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.55  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.55  thf(t17_yellow19, conjecture,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.55             ( v1_subset_1 @
% 0.21/0.55               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.55             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.55             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.55             ( m1_subset_1 @
% 0.21/0.55               B @ 
% 0.21/0.55               ( k1_zfmisc_1 @
% 0.21/0.55                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.55           ( ![C:$i]:
% 0.21/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55               ( ( r3_waybel_9 @
% 0.21/0.55                   A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.21/0.55                 ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]:
% 0.21/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.55            ( l1_pre_topc @ A ) ) =>
% 0.21/0.55          ( ![B:$i]:
% 0.21/0.55            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.55                ( v1_subset_1 @
% 0.21/0.55                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.55                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.55                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.55                ( m1_subset_1 @
% 0.21/0.55                  B @ 
% 0.21/0.55                  ( k1_zfmisc_1 @
% 0.21/0.55                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.55              ( ![C:$i]:
% 0.21/0.55                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55                  ( ( r3_waybel_9 @
% 0.21/0.55                      A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.21/0.55                    ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t17_yellow19])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      ((~ (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.21/0.55        | ~ (r3_waybel_9 @ sk_A @ 
% 0.21/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) | 
% 0.21/0.55       ~
% 0.21/0.55       ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf(dt_l1_pre_topc, axiom,
% 0.21/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.55  thf('2', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.55  thf('3', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.55  thf(dt_k2_struct_0, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_struct_0 @ A ) =>
% 0.21/0.55       ( m1_subset_1 @
% 0.21/0.55         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X4 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k2_struct_0 @ X4) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.21/0.55          | ~ (l1_struct_0 @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_1 @ 
% 0.21/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d2_yellow_1, axiom,
% 0.21/0.55    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_1 @ 
% 0.21/0.55        (k1_zfmisc_1 @ 
% 0.21/0.55         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.55  thf(fc5_yellow19, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.55         ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.55         ( ~( v1_xboole_0 @ C ) ) & 
% 0.21/0.55         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.21/0.55         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.55         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.55         ( m1_subset_1 @
% 0.21/0.55           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.21/0.55       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.21/0.55         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.21/0.55         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.55          | (v1_xboole_0 @ X19)
% 0.21/0.55          | ~ (l1_struct_0 @ X20)
% 0.21/0.55          | (v2_struct_0 @ X20)
% 0.21/0.55          | (v1_xboole_0 @ X21)
% 0.21/0.55          | ~ (v1_subset_1 @ X21 @ (u1_struct_0 @ (k3_yellow_1 @ X19)))
% 0.21/0.55          | ~ (v2_waybel_0 @ X21 @ (k3_yellow_1 @ X19))
% 0.21/0.55          | ~ (v13_waybel_0 @ X21 @ (k3_yellow_1 @ X19))
% 0.21/0.55          | ~ (m1_subset_1 @ X21 @ 
% 0.21/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X19))))
% 0.21/0.55          | (v7_waybel_0 @ (k3_yellow19 @ X20 @ X19 @ X21)))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.55          | (v1_xboole_0 @ X19)
% 0.21/0.55          | ~ (l1_struct_0 @ X20)
% 0.21/0.55          | (v2_struct_0 @ X20)
% 0.21/0.55          | (v1_xboole_0 @ X21)
% 0.21/0.55          | ~ (v1_subset_1 @ X21 @ 
% 0.21/0.55               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X19))))
% 0.21/0.55          | ~ (v2_waybel_0 @ X21 @ (k3_lattice3 @ (k1_lattice3 @ X19)))
% 0.21/0.55          | ~ (v13_waybel_0 @ X21 @ (k3_lattice3 @ (k1_lattice3 @ X19)))
% 0.21/0.55          | ~ (m1_subset_1 @ X21 @ 
% 0.21/0.55               (k1_zfmisc_1 @ 
% 0.21/0.55                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X19)))))
% 0.21/0.55          | (v7_waybel_0 @ (k3_yellow19 @ X20 @ X19 @ X21)))),
% 0.21/0.55      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.55          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.55          | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.21/0.55               (u1_struct_0 @ 
% 0.21/0.55                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.21/0.55          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (l1_struct_0 @ X0)
% 0.21/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['7', '13'])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      ((v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      ((v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.55      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      ((v1_subset_1 @ sk_B_1 @ 
% 0.21/0.55        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      ((v1_subset_1 @ sk_B_1 @ 
% 0.21/0.55        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (l1_struct_0 @ X0)
% 0.21/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '17', '20', '23'])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      ((~ (l1_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '24'])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.55      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '26'])).
% 0.21/0.55  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.55  thf('30', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (![X4 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k2_struct_0 @ X4) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.21/0.55          | ~ (l1_struct_0 @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_1 @ 
% 0.21/0.55        (k1_zfmisc_1 @ 
% 0.21/0.55         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.55  thf(fc4_yellow19, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.55         ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.55         ( ~( v1_xboole_0 @ C ) ) & 
% 0.21/0.55         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.55         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.55         ( m1_subset_1 @
% 0.21/0.55           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.21/0.55       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.21/0.55         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.21/0.55         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.21/0.55         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.55          | (v1_xboole_0 @ X16)
% 0.21/0.55          | ~ (l1_struct_0 @ X17)
% 0.21/0.55          | (v2_struct_0 @ X17)
% 0.21/0.55          | (v1_xboole_0 @ X18)
% 0.21/0.55          | ~ (v2_waybel_0 @ X18 @ (k3_yellow_1 @ X16))
% 0.21/0.55          | ~ (v13_waybel_0 @ X18 @ (k3_yellow_1 @ X16))
% 0.21/0.55          | ~ (m1_subset_1 @ X18 @ 
% 0.21/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X16))))
% 0.21/0.55          | (v4_orders_2 @ (k3_yellow19 @ X17 @ X16 @ X18)))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.55          | (v1_xboole_0 @ X16)
% 0.21/0.55          | ~ (l1_struct_0 @ X17)
% 0.21/0.55          | (v2_struct_0 @ X17)
% 0.21/0.55          | (v1_xboole_0 @ X18)
% 0.21/0.55          | ~ (v2_waybel_0 @ X18 @ (k3_lattice3 @ (k1_lattice3 @ X16)))
% 0.21/0.55          | ~ (v13_waybel_0 @ X18 @ (k3_lattice3 @ (k1_lattice3 @ X16)))
% 0.21/0.55          | ~ (m1_subset_1 @ X18 @ 
% 0.21/0.55               (k1_zfmisc_1 @ 
% 0.21/0.55                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X16)))))
% 0.21/0.55          | (v4_orders_2 @ (k3_yellow19 @ X17 @ X16 @ X18)))),
% 0.21/0.55      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.55          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.55          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (l1_struct_0 @ X0)
% 0.21/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['32', '37'])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      ((v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      ((v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.55      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (l1_struct_0 @ X0)
% 0.21/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.55      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      ((~ (l1_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['31', '41'])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.55      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['30', '43'])).
% 0.21/0.55  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.55  thf('47', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      (![X4 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k2_struct_0 @ X4) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.21/0.55          | ~ (l1_struct_0 @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_1 @ 
% 0.21/0.55        (k1_zfmisc_1 @ 
% 0.21/0.55         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.55  thf(dt_k3_yellow19, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.55         ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.55         ( ~( v1_xboole_0 @ C ) ) & 
% 0.21/0.55         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.55         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.55         ( m1_subset_1 @
% 0.21/0.55           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.21/0.55       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.21/0.55         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.21/0.55         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.55          | (v1_xboole_0 @ X13)
% 0.21/0.55          | ~ (l1_struct_0 @ X14)
% 0.21/0.55          | (v2_struct_0 @ X14)
% 0.21/0.55          | (v1_xboole_0 @ X15)
% 0.21/0.55          | ~ (v2_waybel_0 @ X15 @ (k3_yellow_1 @ X13))
% 0.21/0.55          | ~ (v13_waybel_0 @ X15 @ (k3_yellow_1 @ X13))
% 0.21/0.55          | ~ (m1_subset_1 @ X15 @ 
% 0.21/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X13))))
% 0.21/0.55          | (l1_waybel_0 @ (k3_yellow19 @ X14 @ X13 @ X15) @ X14))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('54', plain,
% 0.21/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.55          | (v1_xboole_0 @ X13)
% 0.21/0.55          | ~ (l1_struct_0 @ X14)
% 0.21/0.55          | (v2_struct_0 @ X14)
% 0.21/0.55          | (v1_xboole_0 @ X15)
% 0.21/0.55          | ~ (v2_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.21/0.55          | ~ (v13_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.21/0.55          | ~ (m1_subset_1 @ X15 @ 
% 0.21/0.55               (k1_zfmisc_1 @ 
% 0.21/0.55                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X13)))))
% 0.21/0.55          | (l1_waybel_0 @ (k3_yellow19 @ X14 @ X13 @ X15) @ X14))),
% 0.21/0.55      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.55           X0)
% 0.21/0.55          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.55          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.55          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (l1_struct_0 @ X0)
% 0.21/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['49', '54'])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      ((v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      ((v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.55      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.55  thf('58', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.55           X0)
% 0.21/0.55          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (l1_struct_0 @ X0)
% 0.21/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.55      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      ((~ (l1_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | (l1_waybel_0 @ 
% 0.21/0.55           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['48', '58'])).
% 0.21/0.55  thf('60', plain,
% 0.21/0.55      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.55         sk_A)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.55      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.55  thf('61', plain,
% 0.21/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | (l1_waybel_0 @ 
% 0.21/0.55           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['47', '60'])).
% 0.21/0.55  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('63', plain,
% 0.21/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | (l1_waybel_0 @ 
% 0.21/0.55           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.55  thf('64', plain,
% 0.21/0.55      (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.21/0.55        | (r3_waybel_9 @ sk_A @ 
% 0.21/0.55           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('65', plain,
% 0.21/0.55      (((r3_waybel_9 @ sk_A @ 
% 0.21/0.55         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))
% 0.21/0.55         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('split', [status(esa)], ['64'])).
% 0.21/0.55  thf('66', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t12_yellow19, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.55             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.55           ( ![C:$i]:
% 0.21/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.55               ( ( r3_waybel_9 @ A @ B @ C ) <=>
% 0.21/0.55                 ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.21/0.55  thf('67', plain,
% 0.21/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X22)
% 0.21/0.55          | ~ (v4_orders_2 @ X22)
% 0.21/0.55          | ~ (v7_waybel_0 @ X22)
% 0.21/0.55          | ~ (l1_waybel_0 @ X22 @ X23)
% 0.21/0.55          | ~ (r3_waybel_9 @ X23 @ X22 @ X24)
% 0.21/0.55          | (r1_waybel_7 @ X23 @ (k2_yellow19 @ X23 @ X22) @ X24)
% 0.21/0.55          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.21/0.55          | ~ (l1_pre_topc @ X23)
% 0.21/0.55          | ~ (v2_pre_topc @ X23)
% 0.21/0.55          | (v2_struct_0 @ X23))),
% 0.21/0.55      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.21/0.55  thf('68', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_struct_0 @ sk_A)
% 0.21/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.21/0.55          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.21/0.55          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.21/0.55          | ~ (v7_waybel_0 @ X0)
% 0.21/0.55          | ~ (v4_orders_2 @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.55  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('71', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_struct_0 @ sk_A)
% 0.21/0.55          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.21/0.55          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.21/0.55          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.21/0.55          | ~ (v7_waybel_0 @ X0)
% 0.21/0.55          | ~ (v4_orders_2 @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.21/0.55  thf('72', plain,
% 0.21/0.55      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55         | ~ (v4_orders_2 @ 
% 0.21/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55         | ~ (v7_waybel_0 @ 
% 0.21/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55         | ~ (l1_waybel_0 @ 
% 0.21/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.21/0.55         | (r1_waybel_7 @ sk_A @ 
% 0.21/0.55            (k2_yellow19 @ sk_A @ 
% 0.21/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.21/0.55            sk_C)
% 0.21/0.55         | (v2_struct_0 @ sk_A)))
% 0.21/0.55         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['65', '71'])).
% 0.21/0.55  thf('73', plain,
% 0.21/0.55      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (r1_waybel_7 @ sk_A @ 
% 0.21/0.55            (k2_yellow19 @ sk_A @ 
% 0.21/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.21/0.55            sk_C)
% 0.21/0.55         | ~ (v7_waybel_0 @ 
% 0.21/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55         | ~ (v4_orders_2 @ 
% 0.21/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 0.21/0.55         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['63', '72'])).
% 0.21/0.55  thf('74', plain,
% 0.21/0.55      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55         | ~ (v4_orders_2 @ 
% 0.21/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55         | ~ (v7_waybel_0 @ 
% 0.21/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55         | (r1_waybel_7 @ sk_A @ 
% 0.21/0.55            (k2_yellow19 @ sk_A @ 
% 0.21/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.21/0.55            sk_C)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ sk_B_1)))
% 0.21/0.55         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['73'])).
% 0.21/0.55  thf('75', plain,
% 0.21/0.55      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (r1_waybel_7 @ sk_A @ 
% 0.21/0.55            (k2_yellow19 @ sk_A @ 
% 0.21/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.21/0.55            sk_C)
% 0.21/0.55         | ~ (v7_waybel_0 @ 
% 0.21/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 0.21/0.55         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['46', '74'])).
% 0.21/0.55  thf('76', plain,
% 0.21/0.55      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55         | ~ (v7_waybel_0 @ 
% 0.21/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55         | (r1_waybel_7 @ sk_A @ 
% 0.21/0.55            (k2_yellow19 @ sk_A @ 
% 0.21/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.21/0.55            sk_C)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ sk_B_1)))
% 0.21/0.55         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['75'])).
% 0.21/0.55  thf('77', plain,
% 0.21/0.55      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (r1_waybel_7 @ sk_A @ 
% 0.21/0.55            (k2_yellow19 @ sk_A @ 
% 0.21/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.21/0.55            sk_C)
% 0.21/0.55         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 0.21/0.55         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['29', '76'])).
% 0.21/0.55  thf('78', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.55  thf('79', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_1 @ 
% 0.21/0.55        (k1_zfmisc_1 @ 
% 0.21/0.55         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.55  thf(t15_yellow19, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.55             ( v1_subset_1 @
% 0.21/0.55               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.55             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.55             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.55             ( m1_subset_1 @
% 0.21/0.55               B @ 
% 0.21/0.55               ( k1_zfmisc_1 @
% 0.21/0.55                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.55           ( ( B ) =
% 0.21/0.55             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.21/0.55  thf('80', plain,
% 0.21/0.55      (![X25 : $i, X26 : $i]:
% 0.21/0.55         ((v1_xboole_0 @ X25)
% 0.21/0.55          | ~ (v1_subset_1 @ X25 @ 
% 0.21/0.55               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X26))))
% 0.21/0.55          | ~ (v2_waybel_0 @ X25 @ (k3_yellow_1 @ (k2_struct_0 @ X26)))
% 0.21/0.55          | ~ (v13_waybel_0 @ X25 @ (k3_yellow_1 @ (k2_struct_0 @ X26)))
% 0.21/0.55          | ~ (m1_subset_1 @ X25 @ 
% 0.21/0.55               (k1_zfmisc_1 @ 
% 0.21/0.55                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X26)))))
% 0.21/0.55          | ((X25)
% 0.21/0.55              = (k2_yellow19 @ X26 @ 
% 0.21/0.55                 (k3_yellow19 @ X26 @ (k2_struct_0 @ X26) @ X25)))
% 0.21/0.55          | ~ (l1_struct_0 @ X26)
% 0.21/0.55          | (v2_struct_0 @ X26))),
% 0.21/0.55      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.21/0.55  thf('81', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('82', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('83', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('84', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('85', plain,
% 0.21/0.55      (![X25 : $i, X26 : $i]:
% 0.21/0.55         ((v1_xboole_0 @ X25)
% 0.21/0.55          | ~ (v1_subset_1 @ X25 @ 
% 0.21/0.55               (u1_struct_0 @ 
% 0.21/0.55                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X26)))))
% 0.21/0.55          | ~ (v2_waybel_0 @ X25 @ 
% 0.21/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X26))))
% 0.21/0.55          | ~ (v13_waybel_0 @ X25 @ 
% 0.21/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X26))))
% 0.21/0.55          | ~ (m1_subset_1 @ X25 @ 
% 0.21/0.55               (k1_zfmisc_1 @ 
% 0.21/0.55                (u1_struct_0 @ 
% 0.21/0.55                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X26))))))
% 0.21/0.55          | ((X25)
% 0.21/0.55              = (k2_yellow19 @ X26 @ 
% 0.21/0.55                 (k3_yellow19 @ X26 @ (k2_struct_0 @ X26) @ X25)))
% 0.21/0.55          | ~ (l1_struct_0 @ X26)
% 0.21/0.55          | (v2_struct_0 @ X26))),
% 0.21/0.55      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.21/0.55  thf('86', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.55        | ((sk_B_1)
% 0.21/0.55            = (k2_yellow19 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.21/0.55        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.55             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.55        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.55             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.55        | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.21/0.55             (u1_struct_0 @ 
% 0.21/0.55              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['79', '85'])).
% 0.21/0.55  thf('87', plain,
% 0.21/0.55      ((v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('88', plain,
% 0.21/0.55      ((v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.55      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.55  thf('89', plain,
% 0.21/0.55      ((v1_subset_1 @ sk_B_1 @ 
% 0.21/0.55        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.55  thf('90', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.55        | ((sk_B_1)
% 0.21/0.55            = (k2_yellow19 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 0.21/0.55  thf('91', plain,
% 0.21/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | ((sk_B_1)
% 0.21/0.55            = (k2_yellow19 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.21/0.55        | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['78', '90'])).
% 0.21/0.55  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('93', plain,
% 0.21/0.55      (((v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | ((sk_B_1)
% 0.21/0.55            = (k2_yellow19 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.21/0.55        | (v2_struct_0 @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['91', '92'])).
% 0.21/0.55  thf('94', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('95', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A)
% 0.21/0.55        | ((sk_B_1)
% 0.21/0.55            = (k2_yellow19 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.21/0.55      inference('clc', [status(thm)], ['93', '94'])).
% 0.21/0.55  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('97', plain,
% 0.21/0.55      (((sk_B_1)
% 0.21/0.55         = (k2_yellow19 @ sk_A @ 
% 0.21/0.55            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.55      inference('clc', [status(thm)], ['95', '96'])).
% 0.21/0.55  thf('98', plain,
% 0.21/0.55      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.21/0.55         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 0.21/0.55         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['77', '97'])).
% 0.21/0.55  thf('99', plain,
% 0.21/0.55      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ sk_B_1)))
% 0.21/0.55         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['98'])).
% 0.21/0.55  thf('100', plain,
% 0.21/0.55      (![X4 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k2_struct_0 @ X4) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.21/0.55          | ~ (l1_struct_0 @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.55  thf('101', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B_1 @ 
% 0.21/0.55        (k1_zfmisc_1 @ 
% 0.21/0.55         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.55  thf('102', plain,
% 0.21/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.55          | (v1_xboole_0 @ X13)
% 0.21/0.55          | ~ (l1_struct_0 @ X14)
% 0.21/0.55          | (v2_struct_0 @ X14)
% 0.21/0.55          | (v1_xboole_0 @ X15)
% 0.21/0.55          | ~ (v2_waybel_0 @ X15 @ (k3_yellow_1 @ X13))
% 0.21/0.55          | ~ (v13_waybel_0 @ X15 @ (k3_yellow_1 @ X13))
% 0.21/0.55          | ~ (m1_subset_1 @ X15 @ 
% 0.21/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X13))))
% 0.21/0.55          | ~ (v2_struct_0 @ (k3_yellow19 @ X14 @ X13 @ X15)))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.21/0.55  thf('103', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('104', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('105', plain,
% 0.21/0.55      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.55  thf('106', plain,
% 0.21/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.55          | (v1_xboole_0 @ X13)
% 0.21/0.55          | ~ (l1_struct_0 @ X14)
% 0.21/0.55          | (v2_struct_0 @ X14)
% 0.21/0.55          | (v1_xboole_0 @ X15)
% 0.21/0.55          | ~ (v2_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.21/0.55          | ~ (v13_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.21/0.55          | ~ (m1_subset_1 @ X15 @ 
% 0.21/0.55               (k1_zfmisc_1 @ 
% 0.21/0.55                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X13)))))
% 0.21/0.55          | ~ (v2_struct_0 @ (k3_yellow19 @ X14 @ X13 @ X15)))),
% 0.21/0.55      inference('demod', [status(thm)], ['102', '103', '104', '105'])).
% 0.21/0.55  thf('107', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.55          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.55          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (l1_struct_0 @ X0)
% 0.21/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['101', '106'])).
% 0.21/0.55  thf('108', plain,
% 0.21/0.55      ((v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('109', plain,
% 0.21/0.55      ((v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.55      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.55  thf('110', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55          | (v2_struct_0 @ X0)
% 0.21/0.55          | ~ (l1_struct_0 @ X0)
% 0.21/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.55      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.21/0.55  thf('111', plain,
% 0.21/0.55      ((~ (l1_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['100', '110'])).
% 0.21/0.55  thf('112', plain,
% 0.21/0.55      ((~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.55      inference('simplify', [status(thm)], ['111'])).
% 0.21/0.55  thf('113', plain,
% 0.21/0.55      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.21/0.55         | ~ (l1_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ sk_B_1)))
% 0.21/0.55         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['99', '112'])).
% 0.21/0.55  thf('114', plain,
% 0.21/0.55      (((~ (l1_struct_0 @ sk_A)
% 0.21/0.55         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ sk_B_1)))
% 0.21/0.55         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['113'])).
% 0.21/0.55  thf('115', plain,
% 0.21/0.55      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))
% 0.21/0.55         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '114'])).
% 0.21/0.55  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('117', plain,
% 0.21/0.55      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))
% 0.21/0.55         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['115', '116'])).
% 0.21/0.55  thf('118', plain,
% 0.21/0.55      ((~ (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C))
% 0.21/0.55         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('119', plain,
% 0.21/0.55      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ sk_B_1)))
% 0.21/0.55         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['117', '118'])).
% 0.21/0.55  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('121', plain,
% 0.21/0.55      ((((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.21/0.55         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('clc', [status(thm)], ['119', '120'])).
% 0.21/0.55  thf('122', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('123', plain,
% 0.21/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.21/0.55         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('clc', [status(thm)], ['121', '122'])).
% 0.21/0.55  thf(t27_tops_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.21/0.55  thf('124', plain,
% 0.21/0.55      (![X9 : $i]:
% 0.21/0.55         (((k2_pre_topc @ X9 @ (k2_struct_0 @ X9)) = (k2_struct_0 @ X9))
% 0.21/0.55          | ~ (l1_pre_topc @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [t27_tops_1])).
% 0.21/0.55  thf('125', plain,
% 0.21/0.55      (![X9 : $i]:
% 0.21/0.55         (((k2_pre_topc @ X9 @ (k2_struct_0 @ X9)) = (k2_struct_0 @ X9))
% 0.21/0.55          | ~ (l1_pre_topc @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [t27_tops_1])).
% 0.21/0.55  thf('126', plain,
% 0.21/0.55      (![X4 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k2_struct_0 @ X4) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.21/0.55          | ~ (l1_struct_0 @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.55  thf(d3_tops_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ( v1_tops_1 @ B @ A ) <=>
% 0.21/0.55             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('127', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.55          | ((k2_pre_topc @ X8 @ X7) != (k2_struct_0 @ X8))
% 0.21/0.55          | (v1_tops_1 @ X7 @ X8)
% 0.21/0.55          | ~ (l1_pre_topc @ X8))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.21/0.55  thf('128', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_struct_0 @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | (v1_tops_1 @ (k2_struct_0 @ X0) @ X0)
% 0.21/0.55          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) != (k2_struct_0 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['126', '127'])).
% 0.21/0.55  thf('129', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k2_struct_0 @ X0) != (k2_struct_0 @ X0))
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | (v1_tops_1 @ (k2_struct_0 @ X0) @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (l1_struct_0 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['125', '128'])).
% 0.21/0.55  thf('130', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_struct_0 @ X0)
% 0.21/0.55          | (v1_tops_1 @ (k2_struct_0 @ X0) @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['129'])).
% 0.21/0.55  thf('131', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.55  thf('132', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X0) | (v1_tops_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.21/0.55      inference('clc', [status(thm)], ['130', '131'])).
% 0.21/0.55  thf('133', plain,
% 0.21/0.55      (![X4 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (k2_struct_0 @ X4) @ 
% 0.21/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.21/0.55          | ~ (l1_struct_0 @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.55  thf(d2_tops_3, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ( v1_tops_1 @ B @ A ) <=>
% 0.21/0.55             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('134', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.55          | ~ (v1_tops_1 @ X11 @ X12)
% 0.21/0.55          | ((k2_pre_topc @ X12 @ X11) = (u1_struct_0 @ X12))
% 0.21/0.55          | ~ (l1_pre_topc @ X12))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.21/0.55  thf('135', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_struct_0 @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.21/0.55          | ~ (v1_tops_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['133', '134'])).
% 0.21/0.55  thf('136', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X0)
% 0.21/0.55          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (l1_struct_0 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['132', '135'])).
% 0.21/0.55  thf('137', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_struct_0 @ X0)
% 0.21/0.55          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.21/0.55          | ~ (l1_pre_topc @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['136'])).
% 0.21/0.55  thf('138', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.55  thf('139', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X0)
% 0.21/0.55          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.21/0.55      inference('clc', [status(thm)], ['137', '138'])).
% 0.21/0.55  thf('140', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0))
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['124', '139'])).
% 0.21/0.55  thf('141', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['140'])).
% 0.21/0.55  thf(rc7_pre_topc, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.55       ( ?[B:$i]:
% 0.21/0.55         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.55           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('142', plain,
% 0.21/0.55      (![X6 : $i]:
% 0.21/0.55         ((m1_subset_1 @ (sk_B @ X6) @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.55          | ~ (l1_pre_topc @ X6)
% 0.21/0.55          | ~ (v2_pre_topc @ X6)
% 0.21/0.55          | (v2_struct_0 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.21/0.55  thf(cc1_subset_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.21/0.55  thf('143', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.21/0.55          | (v1_xboole_0 @ X2)
% 0.21/0.55          | ~ (v1_xboole_0 @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.21/0.55  thf('144', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.21/0.55          | (v1_xboole_0 @ (sk_B @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['142', '143'])).
% 0.21/0.55  thf('145', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | (v1_xboole_0 @ (sk_B @ X0))
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | (v2_struct_0 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['141', '144'])).
% 0.21/0.55  thf('146', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | (v1_xboole_0 @ (sk_B @ X0))
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['145'])).
% 0.21/0.55  thf('147', plain,
% 0.21/0.55      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (sk_B @ sk_A))
% 0.21/0.55         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55         | (v2_struct_0 @ sk_A)))
% 0.21/0.55         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['123', '146'])).
% 0.21/0.55  thf('148', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('149', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('150', plain,
% 0.21/0.55      ((((v1_xboole_0 @ (sk_B @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.21/0.55         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['147', '148', '149'])).
% 0.21/0.55  thf('151', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('152', plain,
% 0.21/0.55      (((v1_xboole_0 @ (sk_B @ sk_A)))
% 0.21/0.55         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('clc', [status(thm)], ['150', '151'])).
% 0.21/0.55  thf('153', plain,
% 0.21/0.55      (![X6 : $i]:
% 0.21/0.55         (~ (v1_xboole_0 @ (sk_B @ X6))
% 0.21/0.55          | ~ (l1_pre_topc @ X6)
% 0.21/0.55          | ~ (v2_pre_topc @ X6)
% 0.21/0.55          | (v2_struct_0 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.21/0.55  thf('154', plain,
% 0.21/0.55      ((((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.55         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['152', '153'])).
% 0.21/0.55  thf('155', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('156', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('157', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A))
% 0.21/0.55         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['154', '155', '156'])).
% 0.21/0.55  thf('158', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('159', plain,
% 0.21/0.55      (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) | 
% 0.21/0.55       ~
% 0.21/0.55       ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))),
% 0.21/0.55      inference('sup-', [status(thm)], ['157', '158'])).
% 0.21/0.55  thf('160', plain,
% 0.21/0.55      (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) | 
% 0.21/0.55       ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))),
% 0.21/0.55      inference('split', [status(esa)], ['64'])).
% 0.21/0.55  thf('161', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.55  thf('162', plain,
% 0.21/0.55      (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C))
% 0.21/0.55         <= (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.55      inference('split', [status(esa)], ['64'])).
% 0.21/0.55  thf('163', plain,
% 0.21/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.55  thf('164', plain,
% 0.21/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.55  thf('165', plain,
% 0.21/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | (l1_waybel_0 @ 
% 0.21/0.55           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.55  thf('166', plain,
% 0.21/0.55      (((sk_B_1)
% 0.21/0.55         = (k2_yellow19 @ sk_A @ 
% 0.21/0.55            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.55      inference('clc', [status(thm)], ['95', '96'])).
% 0.21/0.55  thf('167', plain,
% 0.21/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X22)
% 0.21/0.55          | ~ (v4_orders_2 @ X22)
% 0.21/0.55          | ~ (v7_waybel_0 @ X22)
% 0.21/0.55          | ~ (l1_waybel_0 @ X22 @ X23)
% 0.21/0.55          | ~ (r1_waybel_7 @ X23 @ (k2_yellow19 @ X23 @ X22) @ X24)
% 0.21/0.55          | (r3_waybel_9 @ X23 @ X22 @ X24)
% 0.21/0.55          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.21/0.55          | ~ (l1_pre_topc @ X23)
% 0.21/0.55          | ~ (v2_pre_topc @ X23)
% 0.21/0.55          | (v2_struct_0 @ X23))),
% 0.21/0.55      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.21/0.55  thf('168', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.55          | (v2_struct_0 @ sk_A)
% 0.21/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.21/0.55          | ~ (l1_waybel_0 @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.21/0.55          | ~ (v7_waybel_0 @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | ~ (v4_orders_2 @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['166', '167'])).
% 0.21/0.55  thf('169', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('170', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('171', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.55          | (v2_struct_0 @ sk_A)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.21/0.55          | ~ (l1_waybel_0 @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.21/0.55          | ~ (v7_waybel_0 @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | ~ (v4_orders_2 @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['168', '169', '170'])).
% 0.21/0.55  thf('172', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v1_xboole_0 @ sk_B_1)
% 0.21/0.55          | (v2_struct_0 @ sk_A)
% 0.21/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | ~ (v4_orders_2 @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | ~ (v7_waybel_0 @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A)
% 0.21/0.55          | ~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['165', '171'])).
% 0.21/0.55  thf('173', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.21/0.55          | ~ (v7_waybel_0 @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | ~ (v4_orders_2 @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A)
% 0.21/0.55          | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.55      inference('simplify', [status(thm)], ['172'])).
% 0.21/0.55  thf('174', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v1_xboole_0 @ sk_B_1)
% 0.21/0.55          | (v2_struct_0 @ sk_A)
% 0.21/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55          | (v2_struct_0 @ sk_A)
% 0.21/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | ~ (v4_orders_2 @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['164', '173'])).
% 0.21/0.55  thf('175', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.21/0.55          | ~ (v4_orders_2 @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A)
% 0.21/0.55          | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.55      inference('simplify', [status(thm)], ['174'])).
% 0.21/0.55  thf('176', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v1_xboole_0 @ sk_B_1)
% 0.21/0.55          | (v2_struct_0 @ sk_A)
% 0.21/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55          | (v2_struct_0 @ sk_A)
% 0.21/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | ~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['163', '175'])).
% 0.21/0.55  thf('177', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.55          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.21/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55          | (v2_struct_0 @ sk_A)
% 0.21/0.55          | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.55      inference('simplify', [status(thm)], ['176'])).
% 0.21/0.55  thf('178', plain,
% 0.21/0.55      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55         | (r3_waybel_9 @ sk_A @ 
% 0.21/0.55            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)
% 0.21/0.55         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))))
% 0.21/0.55         <= (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['162', '177'])).
% 0.21/0.55  thf('179', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('180', plain,
% 0.21/0.55      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55         | (r3_waybel_9 @ sk_A @ 
% 0.21/0.55            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))
% 0.21/0.55         <= (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['178', '179'])).
% 0.21/0.55  thf('181', plain,
% 0.21/0.55      ((~ (r3_waybel_9 @ sk_A @ 
% 0.21/0.55           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('182', plain,
% 0.21/0.55      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ sk_B_1)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.55             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['180', '181'])).
% 0.21/0.55  thf('183', plain,
% 0.21/0.55      ((~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.55        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55        | (v2_struct_0 @ sk_A)
% 0.21/0.55        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.55      inference('simplify', [status(thm)], ['111'])).
% 0.21/0.55  thf('184', plain,
% 0.21/0.55      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | ~ (l1_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ sk_B_1)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.55             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['182', '183'])).
% 0.21/0.55  thf('185', plain,
% 0.21/0.55      (((~ (l1_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ sk_B_1)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.55             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['184'])).
% 0.21/0.55  thf('186', plain,
% 0.21/0.55      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.55             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['161', '185'])).
% 0.21/0.55  thf('187', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('188', plain,
% 0.21/0.55      ((((v1_xboole_0 @ sk_B_1)
% 0.21/0.55         | (v2_struct_0 @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.55             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['186', '187'])).
% 0.21/0.55  thf('189', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('190', plain,
% 0.21/0.55      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.55             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.55      inference('clc', [status(thm)], ['188', '189'])).
% 0.21/0.55  thf('191', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('192', plain,
% 0.21/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.55             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.55      inference('clc', [status(thm)], ['190', '191'])).
% 0.21/0.55  thf('193', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((v2_struct_0 @ X0)
% 0.21/0.55          | ~ (v2_pre_topc @ X0)
% 0.21/0.55          | (v1_xboole_0 @ (sk_B @ X0))
% 0.21/0.55          | ~ (l1_pre_topc @ X0)
% 0.21/0.55          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['145'])).
% 0.21/0.55  thf('194', plain,
% 0.21/0.55      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.55         | (v1_xboole_0 @ (sk_B @ sk_A))
% 0.21/0.55         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55         | (v2_struct_0 @ sk_A)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.55             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['192', '193'])).
% 0.21/0.55  thf('195', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('196', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('197', plain,
% 0.21/0.55      ((((v1_xboole_0 @ (sk_B @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.55             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['194', '195', '196'])).
% 0.21/0.55  thf('198', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('199', plain,
% 0.21/0.55      (((v1_xboole_0 @ (sk_B @ sk_A)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.55             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.55      inference('clc', [status(thm)], ['197', '198'])).
% 0.21/0.55  thf('200', plain,
% 0.21/0.55      (![X6 : $i]:
% 0.21/0.55         (~ (v1_xboole_0 @ (sk_B @ X6))
% 0.21/0.55          | ~ (l1_pre_topc @ X6)
% 0.21/0.55          | ~ (v2_pre_topc @ X6)
% 0.21/0.55          | (v2_struct_0 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.21/0.55  thf('201', plain,
% 0.21/0.55      ((((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.55             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['199', '200'])).
% 0.21/0.55  thf('202', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('203', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('204', plain,
% 0.21/0.55      (((v2_struct_0 @ sk_A))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 0.21/0.55             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['201', '202', '203'])).
% 0.21/0.55  thf('205', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('206', plain,
% 0.21/0.55      (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) | 
% 0.21/0.55       ((r3_waybel_9 @ sk_A @ 
% 0.21/0.55         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))),
% 0.21/0.55      inference('sup-', [status(thm)], ['204', '205'])).
% 0.21/0.55  thf('207', plain, ($false),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['1', '159', '160', '206'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
