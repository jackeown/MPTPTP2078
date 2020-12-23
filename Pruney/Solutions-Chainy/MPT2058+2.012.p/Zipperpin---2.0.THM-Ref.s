%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fHgBdWfo4m

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:50 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  240 ( 648 expanded)
%              Number of leaves         :   42 ( 217 expanded)
%              Depth                    :   32
%              Number of atoms          : 3230 (12326 expanded)
%              Number of equality atoms :   47 ( 186 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_xboole_0 @ X17 )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( v1_subset_1 @ X19 @ ( u1_struct_0 @ ( k3_yellow_1 @ X17 ) ) )
      | ~ ( v2_waybel_0 @ X19 @ ( k3_yellow_1 @ X17 ) )
      | ~ ( v13_waybel_0 @ X19 @ ( k3_yellow_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X17 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X18 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('10',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('12',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('13',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('14',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_xboole_0 @ X17 )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( v1_subset_1 @ X19 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) )
      | ~ ( v2_waybel_0 @ X19 @ ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) )
      | ~ ( v13_waybel_0 @ X19 @ ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X18 @ X17 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11','12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('18',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('21',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('24',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['15','18','21','24'])).

thf('26',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','25'])).

thf('27',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('32',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v1_xboole_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v2_waybel_0 @ X16 @ ( k3_yellow_1 @ X14 ) )
      | ~ ( v13_waybel_0 @ X16 @ ( k3_yellow_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X14 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X15 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('35',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('36',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('37',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v1_xboole_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v2_waybel_0 @ X16 @ ( k3_lattice3 @ ( k1_lattice3 @ X14 ) ) )
      | ~ ( v13_waybel_0 @ X16 @ ( k3_lattice3 @ ( k1_lattice3 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X14 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X15 @ X14 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('41',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','42'])).

thf('44',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('49',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('51',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v2_waybel_0 @ X13 @ ( k3_yellow_1 @ X11 ) )
      | ~ ( v13_waybel_0 @ X13 @ ( k3_yellow_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X11 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X12 @ X11 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('52',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('53',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('54',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('55',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v2_waybel_0 @ X13 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) )
      | ~ ( v13_waybel_0 @ X13 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X12 @ X11 @ X13 ) @ X12 ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('58',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','59'])).

thf('61',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['48','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,(
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

thf('68',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v7_waybel_0 @ X20 )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( r3_waybel_9 @ X21 @ X20 @ X22 )
      | ( r1_waybel_7 @ X21 @ ( k2_yellow19 @ X21 @ X20 ) @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('69',plain,(
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
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf('74',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['64','73'])).

thf('75',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['47','75'])).

thf('77',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['30','77'])).

thf('79',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('81',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v1_subset_1 @ X23 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X24 ) ) ) )
      | ~ ( v2_waybel_0 @ X23 @ ( k3_yellow_1 @ ( k2_struct_0 @ X24 ) ) )
      | ~ ( v13_waybel_0 @ X23 @ ( k3_yellow_1 @ ( k2_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X24 ) ) ) ) )
      | ( X23
        = ( k2_yellow19 @ X24 @ ( k3_yellow19 @ X24 @ ( k2_struct_0 @ X24 ) @ X23 ) ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('82',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('83',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('84',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('85',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('86',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v1_subset_1 @ X23 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X24 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X23 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X24 ) ) ) )
      | ~ ( v13_waybel_0 @ X23 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X24 ) ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X24 ) ) ) ) ) )
      | ( X23
        = ( k2_yellow19 @ X24 @ ( k3_yellow19 @ X24 @ ( k2_struct_0 @ X24 ) @ X23 ) ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('89',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('90',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['78','98'])).

thf('100',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('103',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v2_waybel_0 @ X13 @ ( k3_yellow_1 @ X11 ) )
      | ~ ( v13_waybel_0 @ X13 @ ( k3_yellow_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X11 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X12 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('104',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('105',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('106',plain,(
    ! [X8: $i] :
      ( ( k3_yellow_1 @ X8 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('107',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v2_waybel_0 @ X13 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) )
      | ~ ( v13_waybel_0 @ X13 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X12 @ X11 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['102','107'])).

thf('109',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('110',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','111'])).

thf('113',plain,
    ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['100','113'])).

thf('115',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['3','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('120',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf(t27_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('125',plain,(
    ! [X7: $i] :
      ( ( ( k2_pre_topc @ X7 @ ( k2_struct_0 @ X7 ) )
        = ( k2_struct_0 @ X7 ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t27_tops_1])).

thf('126',plain,(
    ! [X7: $i] :
      ( ( ( k2_pre_topc @ X7 @ ( k2_struct_0 @ X7 ) )
        = ( k2_struct_0 @ X7 ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t27_tops_1])).

thf('127',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('128',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( ( k2_pre_topc @ X6 @ X5 )
       != ( k2_struct_0 @ X6 ) )
      | ( v1_tops_1 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
       != ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('135',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v1_tops_1 @ X9 @ X10 )
      | ( ( k2_pre_topc @ X10 @ X9 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['133','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['125','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('143',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['124','144'])).

thf('146',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','149'])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['65'])).

thf('154',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('155',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('156',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['65'])).

thf('157',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('158',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('159',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('160',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('161',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v7_waybel_0 @ X20 )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( r1_waybel_7 @ X21 @ ( k2_yellow19 @ X21 @ X20 ) @ X22 )
      | ( r3_waybel_9 @ X21 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('162',plain,(
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
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['162','163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['159','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['158','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['157','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['156','171'])).

thf('173',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('176',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['112'])).

thf('178',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['155','179'])).

thf('181',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['182','183'])).

thf('185',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('188',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('193',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['154','192'])).

thf('194',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','152','153','195'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fHgBdWfo4m
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:12:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 159 iterations in 0.110s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.40/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.58  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.40/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.58  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.40/0.58  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.40/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.40/0.58  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.40/0.58  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.40/0.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.40/0.58  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.40/0.58  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.40/0.58  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.40/0.58  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.40/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.58  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.40/0.58  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.40/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.58  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.40/0.58  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.40/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.58  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 0.40/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.58  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.40/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(t17_yellow19, conjecture,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.58             ( v1_subset_1 @
% 0.40/0.58               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.58             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.58             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.58             ( m1_subset_1 @
% 0.40/0.58               B @ 
% 0.40/0.58               ( k1_zfmisc_1 @
% 0.40/0.58                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.58           ( ![C:$i]:
% 0.40/0.58             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.58               ( ( r3_waybel_9 @
% 0.40/0.58                   A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.40/0.58                 ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i]:
% 0.40/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.40/0.58            ( l1_pre_topc @ A ) ) =>
% 0.40/0.58          ( ![B:$i]:
% 0.40/0.58            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.58                ( v1_subset_1 @
% 0.40/0.58                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.58                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.58                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.58                ( m1_subset_1 @
% 0.40/0.58                  B @ 
% 0.40/0.58                  ( k1_zfmisc_1 @
% 0.40/0.58                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.58              ( ![C:$i]:
% 0.40/0.58                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.58                  ( ( r3_waybel_9 @
% 0.40/0.58                      A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.40/0.58                    ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t17_yellow19])).
% 0.40/0.58  thf('0', plain,
% 0.40/0.58      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.58        | ~ (r3_waybel_9 @ sk_A @ 
% 0.40/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.40/0.58       ~
% 0.40/0.58       ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.58      inference('split', [status(esa)], ['0'])).
% 0.40/0.58  thf(dt_l1_pre_topc, axiom,
% 0.40/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.40/0.58  thf('2', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.58  thf('3', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.58  thf('4', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.58  thf(dt_k2_struct_0, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( l1_struct_0 @ A ) =>
% 0.40/0.58       ( m1_subset_1 @
% 0.40/0.58         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      (![X2 : $i]:
% 0.40/0.58         ((m1_subset_1 @ (k2_struct_0 @ X2) @ 
% 0.40/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.40/0.58          | ~ (l1_struct_0 @ X2))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.40/0.58  thf('6', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B @ 
% 0.40/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(d2_yellow_1, axiom,
% 0.40/0.58    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B @ 
% 0.40/0.58        (k1_zfmisc_1 @ 
% 0.40/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf(fc5_yellow19, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.40/0.58         ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.40/0.58         ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.58         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.40/0.58         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.58         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.58         ( m1_subset_1 @
% 0.40/0.58           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.40/0.58       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.40/0.58         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.40/0.58         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.40/0.58          | (v1_xboole_0 @ X17)
% 0.40/0.58          | ~ (l1_struct_0 @ X18)
% 0.40/0.58          | (v2_struct_0 @ X18)
% 0.40/0.58          | (v1_xboole_0 @ X19)
% 0.40/0.58          | ~ (v1_subset_1 @ X19 @ (u1_struct_0 @ (k3_yellow_1 @ X17)))
% 0.40/0.58          | ~ (v2_waybel_0 @ X19 @ (k3_yellow_1 @ X17))
% 0.40/0.58          | ~ (v13_waybel_0 @ X19 @ (k3_yellow_1 @ X17))
% 0.40/0.58          | ~ (m1_subset_1 @ X19 @ 
% 0.40/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X17))))
% 0.40/0.58          | (v7_waybel_0 @ (k3_yellow19 @ X18 @ X17 @ X19)))),
% 0.40/0.58      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.40/0.58          | (v1_xboole_0 @ X17)
% 0.40/0.58          | ~ (l1_struct_0 @ X18)
% 0.40/0.58          | (v2_struct_0 @ X18)
% 0.40/0.58          | (v1_xboole_0 @ X19)
% 0.40/0.58          | ~ (v1_subset_1 @ X19 @ 
% 0.40/0.58               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X17))))
% 0.40/0.58          | ~ (v2_waybel_0 @ X19 @ (k3_lattice3 @ (k1_lattice3 @ X17)))
% 0.40/0.58          | ~ (v13_waybel_0 @ X19 @ (k3_lattice3 @ (k1_lattice3 @ X17)))
% 0.40/0.58          | ~ (m1_subset_1 @ X19 @ 
% 0.40/0.58               (k1_zfmisc_1 @ 
% 0.40/0.58                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X17)))))
% 0.40/0.58          | (v7_waybel_0 @ (k3_yellow19 @ X18 @ X17 @ X19)))),
% 0.40/0.58      inference('demod', [status(thm)], ['9', '10', '11', '12', '13'])).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.58          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.58          | ~ (v1_subset_1 @ sk_B @ 
% 0.40/0.58               (u1_struct_0 @ 
% 0.40/0.58                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.40/0.58          | (v1_xboole_0 @ sk_B)
% 0.40/0.58          | (v2_struct_0 @ X0)
% 0.40/0.58          | ~ (l1_struct_0 @ X0)
% 0.40/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['8', '14'])).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('20', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      ((v1_subset_1 @ sk_B @ 
% 0.40/0.58        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('23', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('24', plain,
% 0.40/0.58      ((v1_subset_1 @ sk_B @ 
% 0.40/0.58        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.40/0.58  thf('25', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | (v1_xboole_0 @ sk_B)
% 0.40/0.58          | (v2_struct_0 @ X0)
% 0.40/0.58          | ~ (l1_struct_0 @ X0)
% 0.40/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.58      inference('demod', [status(thm)], ['15', '18', '21', '24'])).
% 0.40/0.58  thf('26', plain,
% 0.40/0.58      ((~ (l1_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ sk_B)
% 0.40/0.58        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['5', '25'])).
% 0.40/0.58  thf('27', plain,
% 0.40/0.58      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58        | (v1_xboole_0 @ sk_B)
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.58      inference('simplify', [status(thm)], ['26'])).
% 0.40/0.58  thf('28', plain,
% 0.40/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ sk_B)
% 0.40/0.58        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['4', '27'])).
% 0.40/0.58  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('30', plain,
% 0.40/0.58      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ sk_B)
% 0.40/0.58        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('demod', [status(thm)], ['28', '29'])).
% 0.40/0.58  thf('31', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.58  thf('32', plain,
% 0.40/0.58      (![X2 : $i]:
% 0.40/0.58         ((m1_subset_1 @ (k2_struct_0 @ X2) @ 
% 0.40/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.40/0.58          | ~ (l1_struct_0 @ X2))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.40/0.58  thf('33', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B @ 
% 0.40/0.58        (k1_zfmisc_1 @ 
% 0.40/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf(fc4_yellow19, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.40/0.58         ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.40/0.58         ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.58         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.58         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.58         ( m1_subset_1 @
% 0.40/0.58           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.40/0.58       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.40/0.58         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.40/0.58         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.40/0.58         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.40/0.58  thf('34', plain,
% 0.40/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.40/0.58          | (v1_xboole_0 @ X14)
% 0.40/0.58          | ~ (l1_struct_0 @ X15)
% 0.40/0.58          | (v2_struct_0 @ X15)
% 0.40/0.58          | (v1_xboole_0 @ X16)
% 0.40/0.58          | ~ (v2_waybel_0 @ X16 @ (k3_yellow_1 @ X14))
% 0.40/0.58          | ~ (v13_waybel_0 @ X16 @ (k3_yellow_1 @ X14))
% 0.40/0.58          | ~ (m1_subset_1 @ X16 @ 
% 0.40/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X14))))
% 0.40/0.58          | (v4_orders_2 @ (k3_yellow19 @ X15 @ X14 @ X16)))),
% 0.40/0.58      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.40/0.58  thf('35', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('36', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('38', plain,
% 0.40/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.40/0.58          | (v1_xboole_0 @ X14)
% 0.40/0.58          | ~ (l1_struct_0 @ X15)
% 0.40/0.58          | (v2_struct_0 @ X15)
% 0.40/0.58          | (v1_xboole_0 @ X16)
% 0.40/0.58          | ~ (v2_waybel_0 @ X16 @ (k3_lattice3 @ (k1_lattice3 @ X14)))
% 0.40/0.58          | ~ (v13_waybel_0 @ X16 @ (k3_lattice3 @ (k1_lattice3 @ X14)))
% 0.40/0.58          | ~ (m1_subset_1 @ X16 @ 
% 0.40/0.58               (k1_zfmisc_1 @ 
% 0.40/0.58                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X14)))))
% 0.40/0.58          | (v4_orders_2 @ (k3_yellow19 @ X15 @ X14 @ X16)))),
% 0.40/0.58      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.40/0.58  thf('39', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.58          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.58          | (v1_xboole_0 @ sk_B)
% 0.40/0.58          | (v2_struct_0 @ X0)
% 0.40/0.58          | ~ (l1_struct_0 @ X0)
% 0.40/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['33', '38'])).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.40/0.58  thf('41', plain,
% 0.40/0.58      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.40/0.58  thf('42', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | (v1_xboole_0 @ sk_B)
% 0.40/0.58          | (v2_struct_0 @ X0)
% 0.40/0.58          | ~ (l1_struct_0 @ X0)
% 0.40/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.58      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.40/0.58  thf('43', plain,
% 0.40/0.58      ((~ (l1_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ sk_B)
% 0.40/0.58        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['32', '42'])).
% 0.40/0.58  thf('44', plain,
% 0.40/0.58      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58        | (v1_xboole_0 @ sk_B)
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.58      inference('simplify', [status(thm)], ['43'])).
% 0.40/0.58  thf('45', plain,
% 0.40/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ sk_B)
% 0.40/0.58        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['31', '44'])).
% 0.40/0.58  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('47', plain,
% 0.40/0.58      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ sk_B)
% 0.40/0.58        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('demod', [status(thm)], ['45', '46'])).
% 0.40/0.58  thf('48', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.58  thf('49', plain,
% 0.40/0.58      (![X2 : $i]:
% 0.40/0.58         ((m1_subset_1 @ (k2_struct_0 @ X2) @ 
% 0.40/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.40/0.58          | ~ (l1_struct_0 @ X2))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.40/0.58  thf('50', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B @ 
% 0.40/0.58        (k1_zfmisc_1 @ 
% 0.40/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf(dt_k3_yellow19, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.40/0.58         ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.40/0.58         ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.58         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.58         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.58         ( m1_subset_1 @
% 0.40/0.58           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.40/0.58       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.40/0.58         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.40/0.58         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.40/0.58  thf('51', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.40/0.58          | (v1_xboole_0 @ X11)
% 0.40/0.58          | ~ (l1_struct_0 @ X12)
% 0.40/0.58          | (v2_struct_0 @ X12)
% 0.40/0.58          | (v1_xboole_0 @ X13)
% 0.40/0.58          | ~ (v2_waybel_0 @ X13 @ (k3_yellow_1 @ X11))
% 0.40/0.58          | ~ (v13_waybel_0 @ X13 @ (k3_yellow_1 @ X11))
% 0.40/0.58          | ~ (m1_subset_1 @ X13 @ 
% 0.40/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X11))))
% 0.40/0.58          | (l1_waybel_0 @ (k3_yellow19 @ X12 @ X11 @ X13) @ X12))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.40/0.58  thf('52', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('53', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('54', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('55', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.40/0.58          | (v1_xboole_0 @ X11)
% 0.40/0.58          | ~ (l1_struct_0 @ X12)
% 0.40/0.58          | (v2_struct_0 @ X12)
% 0.40/0.58          | (v1_xboole_0 @ X13)
% 0.40/0.58          | ~ (v2_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.40/0.58          | ~ (v13_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.40/0.58          | ~ (m1_subset_1 @ X13 @ 
% 0.40/0.58               (k1_zfmisc_1 @ 
% 0.40/0.58                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X11)))))
% 0.40/0.58          | (l1_waybel_0 @ (k3_yellow19 @ X12 @ X11 @ X13) @ X12))),
% 0.40/0.58      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.40/0.58  thf('56', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.58          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.58          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.58          | (v1_xboole_0 @ sk_B)
% 0.40/0.58          | (v2_struct_0 @ X0)
% 0.40/0.58          | ~ (l1_struct_0 @ X0)
% 0.40/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['50', '55'])).
% 0.40/0.58  thf('57', plain,
% 0.40/0.58      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.40/0.58  thf('58', plain,
% 0.40/0.58      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.40/0.58  thf('59', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.58          | (v1_xboole_0 @ sk_B)
% 0.40/0.58          | (v2_struct_0 @ X0)
% 0.40/0.58          | ~ (l1_struct_0 @ X0)
% 0.40/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.58      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.40/0.58  thf('60', plain,
% 0.40/0.58      ((~ (l1_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ sk_B)
% 0.40/0.58        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.58           sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['49', '59'])).
% 0.40/0.58  thf('61', plain,
% 0.40/0.58      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.58         sk_A)
% 0.40/0.58        | (v1_xboole_0 @ sk_B)
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.58      inference('simplify', [status(thm)], ['60'])).
% 0.40/0.58  thf('62', plain,
% 0.40/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ sk_B)
% 0.40/0.58        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.58           sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['48', '61'])).
% 0.40/0.58  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('64', plain,
% 0.40/0.58      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ sk_B)
% 0.40/0.58        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.58           sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['62', '63'])).
% 0.40/0.58  thf('65', plain,
% 0.40/0.58      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.58        | (r3_waybel_9 @ sk_A @ 
% 0.40/0.58           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('66', plain,
% 0.40/0.58      (((r3_waybel_9 @ sk_A @ 
% 0.40/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.40/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('split', [status(esa)], ['65'])).
% 0.40/0.58  thf('67', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t12_yellow19, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.40/0.58             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.40/0.58           ( ![C:$i]:
% 0.40/0.58             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.58               ( ( r3_waybel_9 @ A @ B @ C ) <=>
% 0.40/0.58                 ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.40/0.58  thf('68', plain,
% 0.40/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.40/0.58         ((v2_struct_0 @ X20)
% 0.40/0.58          | ~ (v4_orders_2 @ X20)
% 0.40/0.58          | ~ (v7_waybel_0 @ X20)
% 0.40/0.58          | ~ (l1_waybel_0 @ X20 @ X21)
% 0.40/0.58          | ~ (r3_waybel_9 @ X21 @ X20 @ X22)
% 0.40/0.58          | (r1_waybel_7 @ X21 @ (k2_yellow19 @ X21 @ X20) @ X22)
% 0.40/0.58          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.40/0.58          | ~ (l1_pre_topc @ X21)
% 0.40/0.58          | ~ (v2_pre_topc @ X21)
% 0.40/0.58          | (v2_struct_0 @ X21))),
% 0.40/0.58      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.40/0.58  thf('69', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v2_struct_0 @ sk_A)
% 0.40/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.40/0.58          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.40/0.58          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.40/0.58          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.40/0.58          | ~ (v7_waybel_0 @ X0)
% 0.40/0.58          | ~ (v4_orders_2 @ X0)
% 0.40/0.58          | (v2_struct_0 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['67', '68'])).
% 0.40/0.58  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('72', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v2_struct_0 @ sk_A)
% 0.40/0.58          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.40/0.58          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.40/0.58          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.40/0.58          | ~ (v7_waybel_0 @ X0)
% 0.40/0.58          | ~ (v4_orders_2 @ X0)
% 0.40/0.58          | (v2_struct_0 @ X0))),
% 0.40/0.58      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.40/0.58  thf('73', plain,
% 0.40/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58         | ~ (l1_waybel_0 @ 
% 0.40/0.58              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.40/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.58            (k2_yellow19 @ sk_A @ 
% 0.40/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.58            sk_C)
% 0.40/0.58         | (v2_struct_0 @ sk_A)))
% 0.40/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['66', '72'])).
% 0.40/0.58  thf('74', plain,
% 0.40/0.58      ((((v1_xboole_0 @ sk_B)
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.58            (k2_yellow19 @ sk_A @ 
% 0.40/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.58            sk_C)
% 0.40/0.58         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['64', '73'])).
% 0.40/0.58  thf('75', plain,
% 0.40/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.58            (k2_yellow19 @ sk_A @ 
% 0.40/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.58            sk_C)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ sk_B)))
% 0.40/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['74'])).
% 0.40/0.58  thf('76', plain,
% 0.40/0.58      ((((v1_xboole_0 @ sk_B)
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (v1_xboole_0 @ sk_B)
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.58            (k2_yellow19 @ sk_A @ 
% 0.40/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.58            sk_C)
% 0.40/0.58         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['47', '75'])).
% 0.40/0.58  thf('77', plain,
% 0.40/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.58            (k2_yellow19 @ sk_A @ 
% 0.40/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.58            sk_C)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ sk_B)))
% 0.40/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['76'])).
% 0.40/0.58  thf('78', plain,
% 0.40/0.58      ((((v1_xboole_0 @ sk_B)
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (v1_xboole_0 @ sk_B)
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.58            (k2_yellow19 @ sk_A @ 
% 0.40/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.58            sk_C)
% 0.40/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['30', '77'])).
% 0.40/0.58  thf('79', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.58  thf('80', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B @ 
% 0.40/0.58        (k1_zfmisc_1 @ 
% 0.40/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf(t15_yellow19, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.58             ( v1_subset_1 @
% 0.40/0.58               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.58             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.58             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.58             ( m1_subset_1 @
% 0.40/0.58               B @ 
% 0.40/0.58               ( k1_zfmisc_1 @
% 0.40/0.58                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.58           ( ( B ) =
% 0.40/0.58             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.40/0.58  thf('81', plain,
% 0.40/0.58      (![X23 : $i, X24 : $i]:
% 0.40/0.58         ((v1_xboole_0 @ X23)
% 0.40/0.58          | ~ (v1_subset_1 @ X23 @ 
% 0.40/0.58               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X24))))
% 0.40/0.58          | ~ (v2_waybel_0 @ X23 @ (k3_yellow_1 @ (k2_struct_0 @ X24)))
% 0.40/0.58          | ~ (v13_waybel_0 @ X23 @ (k3_yellow_1 @ (k2_struct_0 @ X24)))
% 0.40/0.58          | ~ (m1_subset_1 @ X23 @ 
% 0.40/0.58               (k1_zfmisc_1 @ 
% 0.40/0.58                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X24)))))
% 0.40/0.58          | ((X23)
% 0.40/0.58              = (k2_yellow19 @ X24 @ 
% 0.40/0.58                 (k3_yellow19 @ X24 @ (k2_struct_0 @ X24) @ X23)))
% 0.40/0.58          | ~ (l1_struct_0 @ X24)
% 0.40/0.58          | (v2_struct_0 @ X24))),
% 0.40/0.58      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.40/0.58  thf('82', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('83', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('84', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('85', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('86', plain,
% 0.40/0.58      (![X23 : $i, X24 : $i]:
% 0.40/0.58         ((v1_xboole_0 @ X23)
% 0.40/0.58          | ~ (v1_subset_1 @ X23 @ 
% 0.40/0.58               (u1_struct_0 @ 
% 0.40/0.58                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X24)))))
% 0.40/0.58          | ~ (v2_waybel_0 @ X23 @ 
% 0.40/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X24))))
% 0.40/0.58          | ~ (v13_waybel_0 @ X23 @ 
% 0.40/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X24))))
% 0.40/0.58          | ~ (m1_subset_1 @ X23 @ 
% 0.40/0.58               (k1_zfmisc_1 @ 
% 0.40/0.58                (u1_struct_0 @ 
% 0.40/0.58                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X24))))))
% 0.40/0.58          | ((X23)
% 0.40/0.58              = (k2_yellow19 @ X24 @ 
% 0.40/0.58                 (k3_yellow19 @ X24 @ (k2_struct_0 @ X24) @ X23)))
% 0.40/0.58          | ~ (l1_struct_0 @ X24)
% 0.40/0.58          | (v2_struct_0 @ X24))),
% 0.40/0.58      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 0.40/0.58  thf('87', plain,
% 0.40/0.58      (((v2_struct_0 @ sk_A)
% 0.40/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.58        | ((sk_B)
% 0.40/0.58            = (k2_yellow19 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.58        | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.58             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.58        | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.58             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.58        | ~ (v1_subset_1 @ sk_B @ 
% 0.40/0.58             (u1_struct_0 @ 
% 0.40/0.58              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.40/0.58        | (v1_xboole_0 @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['80', '86'])).
% 0.40/0.58  thf('88', plain,
% 0.40/0.58      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.40/0.58  thf('89', plain,
% 0.40/0.58      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.40/0.58  thf('90', plain,
% 0.40/0.58      ((v1_subset_1 @ sk_B @ 
% 0.40/0.58        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.40/0.58  thf('91', plain,
% 0.40/0.58      (((v2_struct_0 @ sk_A)
% 0.40/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.58        | ((sk_B)
% 0.40/0.58            = (k2_yellow19 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.58        | (v1_xboole_0 @ sk_B))),
% 0.40/0.58      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 0.40/0.58  thf('92', plain,
% 0.40/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ sk_B)
% 0.40/0.58        | ((sk_B)
% 0.40/0.58            = (k2_yellow19 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.58        | (v2_struct_0 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['79', '91'])).
% 0.40/0.58  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('94', plain,
% 0.40/0.58      (((v1_xboole_0 @ sk_B)
% 0.40/0.58        | ((sk_B)
% 0.40/0.58            = (k2_yellow19 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.58        | (v2_struct_0 @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['92', '93'])).
% 0.40/0.58  thf('95', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('96', plain,
% 0.40/0.58      (((v2_struct_0 @ sk_A)
% 0.40/0.58        | ((sk_B)
% 0.40/0.58            = (k2_yellow19 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.40/0.58      inference('clc', [status(thm)], ['94', '95'])).
% 0.40/0.58  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('98', plain,
% 0.40/0.58      (((sk_B)
% 0.40/0.58         = (k2_yellow19 @ sk_A @ 
% 0.40/0.58            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('clc', [status(thm)], ['96', '97'])).
% 0.40/0.58  thf('99', plain,
% 0.40/0.58      ((((v1_xboole_0 @ sk_B)
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (v1_xboole_0 @ sk_B)
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('demod', [status(thm)], ['78', '98'])).
% 0.40/0.58  thf('100', plain,
% 0.40/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ sk_B)))
% 0.40/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['99'])).
% 0.40/0.58  thf('101', plain,
% 0.40/0.58      (![X2 : $i]:
% 0.40/0.58         ((m1_subset_1 @ (k2_struct_0 @ X2) @ 
% 0.40/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.40/0.58          | ~ (l1_struct_0 @ X2))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.40/0.58  thf('102', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B @ 
% 0.40/0.58        (k1_zfmisc_1 @ 
% 0.40/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf('103', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.40/0.58          | (v1_xboole_0 @ X11)
% 0.40/0.58          | ~ (l1_struct_0 @ X12)
% 0.40/0.58          | (v2_struct_0 @ X12)
% 0.40/0.58          | (v1_xboole_0 @ X13)
% 0.40/0.58          | ~ (v2_waybel_0 @ X13 @ (k3_yellow_1 @ X11))
% 0.40/0.58          | ~ (v13_waybel_0 @ X13 @ (k3_yellow_1 @ X11))
% 0.40/0.58          | ~ (m1_subset_1 @ X13 @ 
% 0.40/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X11))))
% 0.40/0.58          | ~ (v2_struct_0 @ (k3_yellow19 @ X12 @ X11 @ X13)))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.40/0.58  thf('104', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('105', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('106', plain,
% 0.40/0.58      (![X8 : $i]: ((k3_yellow_1 @ X8) = (k3_lattice3 @ (k1_lattice3 @ X8)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.58  thf('107', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.40/0.58          | (v1_xboole_0 @ X11)
% 0.40/0.58          | ~ (l1_struct_0 @ X12)
% 0.40/0.58          | (v2_struct_0 @ X12)
% 0.40/0.58          | (v1_xboole_0 @ X13)
% 0.40/0.58          | ~ (v2_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.40/0.58          | ~ (v13_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.40/0.58          | ~ (m1_subset_1 @ X13 @ 
% 0.40/0.58               (k1_zfmisc_1 @ 
% 0.40/0.58                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X11)))))
% 0.40/0.58          | ~ (v2_struct_0 @ (k3_yellow19 @ X12 @ X11 @ X13)))),
% 0.40/0.58      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 0.40/0.58  thf('108', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.58          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.58          | (v1_xboole_0 @ sk_B)
% 0.40/0.58          | (v2_struct_0 @ X0)
% 0.40/0.58          | ~ (l1_struct_0 @ X0)
% 0.40/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['102', '107'])).
% 0.40/0.58  thf('109', plain,
% 0.40/0.58      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.40/0.58  thf('110', plain,
% 0.40/0.58      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.40/0.58  thf('111', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | (v1_xboole_0 @ sk_B)
% 0.40/0.58          | (v2_struct_0 @ X0)
% 0.40/0.58          | ~ (l1_struct_0 @ X0)
% 0.40/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.58      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.40/0.58  thf('112', plain,
% 0.40/0.58      ((~ (l1_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ sk_B)
% 0.40/0.58        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['101', '111'])).
% 0.40/0.58  thf('113', plain,
% 0.40/0.58      ((~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58        | (v1_xboole_0 @ sk_B)
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.58      inference('simplify', [status(thm)], ['112'])).
% 0.40/0.58  thf('114', plain,
% 0.40/0.58      ((((v1_xboole_0 @ sk_B)
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.58         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ sk_B)))
% 0.40/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['100', '113'])).
% 0.40/0.58  thf('115', plain,
% 0.40/0.58      (((~ (l1_struct_0 @ sk_A)
% 0.40/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ sk_B)))
% 0.40/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['114'])).
% 0.40/0.58  thf('116', plain,
% 0.40/0.58      (((~ (l1_pre_topc @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ sk_B)
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.40/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['3', '115'])).
% 0.40/0.58  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('118', plain,
% 0.40/0.58      ((((v1_xboole_0 @ sk_B)
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.40/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('demod', [status(thm)], ['116', '117'])).
% 0.40/0.58  thf('119', plain,
% 0.40/0.58      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.40/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.58      inference('split', [status(esa)], ['0'])).
% 0.40/0.58  thf('120', plain,
% 0.40/0.58      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ sk_B)))
% 0.40/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['118', '119'])).
% 0.40/0.58  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('122', plain,
% 0.40/0.58      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.40/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('clc', [status(thm)], ['120', '121'])).
% 0.40/0.58  thf('123', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('124', plain,
% 0.40/0.58      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.40/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('clc', [status(thm)], ['122', '123'])).
% 0.40/0.58  thf(t27_tops_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( l1_pre_topc @ A ) =>
% 0.40/0.58       ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.40/0.58  thf('125', plain,
% 0.40/0.58      (![X7 : $i]:
% 0.40/0.58         (((k2_pre_topc @ X7 @ (k2_struct_0 @ X7)) = (k2_struct_0 @ X7))
% 0.40/0.58          | ~ (l1_pre_topc @ X7))),
% 0.40/0.58      inference('cnf', [status(esa)], [t27_tops_1])).
% 0.40/0.58  thf('126', plain,
% 0.40/0.58      (![X7 : $i]:
% 0.40/0.58         (((k2_pre_topc @ X7 @ (k2_struct_0 @ X7)) = (k2_struct_0 @ X7))
% 0.40/0.58          | ~ (l1_pre_topc @ X7))),
% 0.40/0.58      inference('cnf', [status(esa)], [t27_tops_1])).
% 0.40/0.58  thf('127', plain,
% 0.40/0.58      (![X2 : $i]:
% 0.40/0.58         ((m1_subset_1 @ (k2_struct_0 @ X2) @ 
% 0.40/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.40/0.58          | ~ (l1_struct_0 @ X2))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.40/0.58  thf(d3_tops_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( l1_pre_topc @ A ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.58           ( ( v1_tops_1 @ B @ A ) <=>
% 0.40/0.58             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.40/0.58  thf('128', plain,
% 0.40/0.58      (![X5 : $i, X6 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.40/0.58          | ((k2_pre_topc @ X6 @ X5) != (k2_struct_0 @ X6))
% 0.40/0.58          | (v1_tops_1 @ X5 @ X6)
% 0.40/0.58          | ~ (l1_pre_topc @ X6))),
% 0.40/0.58      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.40/0.58  thf('129', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (l1_struct_0 @ X0)
% 0.40/0.58          | ~ (l1_pre_topc @ X0)
% 0.40/0.58          | (v1_tops_1 @ (k2_struct_0 @ X0) @ X0)
% 0.40/0.58          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) != (k2_struct_0 @ X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['127', '128'])).
% 0.40/0.58  thf('130', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k2_struct_0 @ X0) != (k2_struct_0 @ X0))
% 0.40/0.58          | ~ (l1_pre_topc @ X0)
% 0.40/0.58          | (v1_tops_1 @ (k2_struct_0 @ X0) @ X0)
% 0.40/0.58          | ~ (l1_pre_topc @ X0)
% 0.40/0.58          | ~ (l1_struct_0 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['126', '129'])).
% 0.40/0.58  thf('131', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (l1_struct_0 @ X0)
% 0.40/0.58          | (v1_tops_1 @ (k2_struct_0 @ X0) @ X0)
% 0.40/0.58          | ~ (l1_pre_topc @ X0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['130'])).
% 0.40/0.58  thf('132', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.58  thf('133', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (l1_pre_topc @ X0) | (v1_tops_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.40/0.58      inference('clc', [status(thm)], ['131', '132'])).
% 0.40/0.58  thf('134', plain,
% 0.40/0.58      (![X2 : $i]:
% 0.40/0.58         ((m1_subset_1 @ (k2_struct_0 @ X2) @ 
% 0.40/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.40/0.58          | ~ (l1_struct_0 @ X2))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.40/0.58  thf(d2_tops_3, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( l1_pre_topc @ A ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.58           ( ( v1_tops_1 @ B @ A ) <=>
% 0.40/0.58             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.40/0.58  thf('135', plain,
% 0.40/0.58      (![X9 : $i, X10 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.40/0.58          | ~ (v1_tops_1 @ X9 @ X10)
% 0.40/0.58          | ((k2_pre_topc @ X10 @ X9) = (u1_struct_0 @ X10))
% 0.40/0.58          | ~ (l1_pre_topc @ X10))),
% 0.40/0.58      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.40/0.58  thf('136', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (l1_struct_0 @ X0)
% 0.40/0.58          | ~ (l1_pre_topc @ X0)
% 0.40/0.58          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.40/0.58          | ~ (v1_tops_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['134', '135'])).
% 0.40/0.58  thf('137', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (l1_pre_topc @ X0)
% 0.40/0.58          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.40/0.58          | ~ (l1_pre_topc @ X0)
% 0.40/0.58          | ~ (l1_struct_0 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['133', '136'])).
% 0.40/0.58  thf('138', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (l1_struct_0 @ X0)
% 0.40/0.58          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.40/0.58          | ~ (l1_pre_topc @ X0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['137'])).
% 0.40/0.58  thf('139', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.58  thf('140', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (l1_pre_topc @ X0)
% 0.40/0.58          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.40/0.58      inference('clc', [status(thm)], ['138', '139'])).
% 0.40/0.58  thf('141', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0))
% 0.40/0.58          | ~ (l1_pre_topc @ X0)
% 0.40/0.58          | ~ (l1_pre_topc @ X0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['125', '140'])).
% 0.40/0.58  thf('142', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (l1_pre_topc @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['141'])).
% 0.40/0.58  thf(fc2_struct_0, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.40/0.58       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.40/0.58  thf('143', plain,
% 0.40/0.58      (![X4 : $i]:
% 0.40/0.58         (~ (v1_xboole_0 @ (u1_struct_0 @ X4))
% 0.40/0.58          | ~ (l1_struct_0 @ X4)
% 0.40/0.58          | (v2_struct_0 @ X4))),
% 0.40/0.58      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.40/0.58  thf('144', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.40/0.58          | ~ (l1_pre_topc @ X0)
% 0.40/0.58          | (v2_struct_0 @ X0)
% 0.40/0.58          | ~ (l1_struct_0 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['142', '143'])).
% 0.40/0.58  thf('145', plain,
% 0.40/0.58      (((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.40/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['124', '144'])).
% 0.40/0.58  thf('146', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('147', plain,
% 0.40/0.58      (((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.40/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('demod', [status(thm)], ['145', '146'])).
% 0.40/0.58  thf('148', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('149', plain,
% 0.40/0.58      ((~ (l1_struct_0 @ sk_A))
% 0.40/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('clc', [status(thm)], ['147', '148'])).
% 0.40/0.58  thf('150', plain,
% 0.40/0.58      ((~ (l1_pre_topc @ sk_A))
% 0.40/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['2', '149'])).
% 0.40/0.58  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('152', plain,
% 0.40/0.58      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.40/0.58       ~
% 0.40/0.58       ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.58      inference('demod', [status(thm)], ['150', '151'])).
% 0.40/0.58  thf('153', plain,
% 0.40/0.58      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.40/0.58       ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.58      inference('split', [status(esa)], ['65'])).
% 0.40/0.58  thf('154', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.58  thf('155', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.58  thf('156', plain,
% 0.40/0.58      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.40/0.58         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.58      inference('split', [status(esa)], ['65'])).
% 0.40/0.58  thf('157', plain,
% 0.40/0.58      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ sk_B)
% 0.40/0.58        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('demod', [status(thm)], ['45', '46'])).
% 0.40/0.58  thf('158', plain,
% 0.40/0.58      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ sk_B)
% 0.40/0.58        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('demod', [status(thm)], ['28', '29'])).
% 0.40/0.58  thf('159', plain,
% 0.40/0.58      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ sk_B)
% 0.40/0.58        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.58           sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['62', '63'])).
% 0.40/0.58  thf('160', plain,
% 0.40/0.58      (((sk_B)
% 0.40/0.58         = (k2_yellow19 @ sk_A @ 
% 0.40/0.58            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('clc', [status(thm)], ['96', '97'])).
% 0.40/0.58  thf('161', plain,
% 0.40/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.40/0.58         ((v2_struct_0 @ X20)
% 0.40/0.58          | ~ (v4_orders_2 @ X20)
% 0.40/0.58          | ~ (v7_waybel_0 @ X20)
% 0.40/0.58          | ~ (l1_waybel_0 @ X20 @ X21)
% 0.40/0.58          | ~ (r1_waybel_7 @ X21 @ (k2_yellow19 @ X21 @ X20) @ X22)
% 0.40/0.58          | (r3_waybel_9 @ X21 @ X20 @ X22)
% 0.40/0.58          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.40/0.58          | ~ (l1_pre_topc @ X21)
% 0.40/0.58          | ~ (v2_pre_topc @ X21)
% 0.40/0.58          | (v2_struct_0 @ X21))),
% 0.40/0.58      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.40/0.58  thf('162', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.58          | (v2_struct_0 @ sk_A)
% 0.40/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.58          | ~ (l1_waybel_0 @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.40/0.58          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['160', '161'])).
% 0.40/0.58  thf('163', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('164', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('165', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.58          | (v2_struct_0 @ sk_A)
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.58          | ~ (l1_waybel_0 @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.40/0.58          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('demod', [status(thm)], ['162', '163', '164'])).
% 0.40/0.58  thf('166', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v1_xboole_0 @ sk_B)
% 0.40/0.58          | (v2_struct_0 @ sk_A)
% 0.40/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.58          | (v2_struct_0 @ sk_A)
% 0.40/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['159', '165'])).
% 0.40/0.58  thf('167', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.58          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58          | (v2_struct_0 @ sk_A)
% 0.40/0.58          | (v1_xboole_0 @ sk_B))),
% 0.40/0.58      inference('simplify', [status(thm)], ['166'])).
% 0.40/0.58  thf('168', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v1_xboole_0 @ sk_B)
% 0.40/0.58          | (v2_struct_0 @ sk_A)
% 0.40/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58          | (v1_xboole_0 @ sk_B)
% 0.40/0.58          | (v2_struct_0 @ sk_A)
% 0.40/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['158', '167'])).
% 0.40/0.58  thf('169', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58          | (v2_struct_0 @ sk_A)
% 0.40/0.58          | (v1_xboole_0 @ sk_B))),
% 0.40/0.58      inference('simplify', [status(thm)], ['168'])).
% 0.40/0.58  thf('170', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v1_xboole_0 @ sk_B)
% 0.40/0.58          | (v2_struct_0 @ sk_A)
% 0.40/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58          | (v1_xboole_0 @ sk_B)
% 0.40/0.58          | (v2_struct_0 @ sk_A)
% 0.40/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['157', '169'])).
% 0.40/0.58  thf('171', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58          | (v2_struct_0 @ sk_A)
% 0.40/0.58          | (v1_xboole_0 @ sk_B))),
% 0.40/0.58      inference('simplify', [status(thm)], ['170'])).
% 0.40/0.58  thf('172', plain,
% 0.40/0.58      ((((v1_xboole_0 @ sk_B)
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58         | (r3_waybel_9 @ sk_A @ 
% 0.40/0.58            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.40/0.58         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))))
% 0.40/0.58         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['156', '171'])).
% 0.40/0.58  thf('173', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('174', plain,
% 0.40/0.58      ((((v1_xboole_0 @ sk_B)
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58         | (r3_waybel_9 @ sk_A @ 
% 0.40/0.58            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))
% 0.40/0.58         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.58      inference('demod', [status(thm)], ['172', '173'])).
% 0.40/0.58  thf('175', plain,
% 0.40/0.58      ((~ (r3_waybel_9 @ sk_A @ 
% 0.40/0.58           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.40/0.58         <= (~
% 0.40/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.58      inference('split', [status(esa)], ['0'])).
% 0.40/0.58  thf('176', plain,
% 0.40/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ sk_B)))
% 0.40/0.58         <= (~
% 0.40/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['174', '175'])).
% 0.40/0.58  thf('177', plain,
% 0.40/0.58      ((~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.58        | (v1_xboole_0 @ sk_B)
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.58      inference('simplify', [status(thm)], ['112'])).
% 0.40/0.58  thf('178', plain,
% 0.40/0.58      ((((v1_xboole_0 @ sk_B)
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ sk_B)))
% 0.40/0.58         <= (~
% 0.40/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['176', '177'])).
% 0.40/0.58  thf('179', plain,
% 0.40/0.58      (((~ (l1_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ sk_B)))
% 0.40/0.58         <= (~
% 0.40/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['178'])).
% 0.40/0.58  thf('180', plain,
% 0.40/0.58      (((~ (l1_pre_topc @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ sk_B)
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.40/0.58         <= (~
% 0.40/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['155', '179'])).
% 0.40/0.58  thf('181', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('182', plain,
% 0.40/0.58      ((((v1_xboole_0 @ sk_B)
% 0.40/0.58         | (v2_struct_0 @ sk_A)
% 0.40/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.40/0.58         <= (~
% 0.40/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.58      inference('demod', [status(thm)], ['180', '181'])).
% 0.40/0.58  thf('183', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('184', plain,
% 0.40/0.58      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.40/0.58         <= (~
% 0.40/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.58      inference('clc', [status(thm)], ['182', '183'])).
% 0.40/0.58  thf('185', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('186', plain,
% 0.40/0.58      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.40/0.58         <= (~
% 0.40/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.58      inference('clc', [status(thm)], ['184', '185'])).
% 0.40/0.58  thf('187', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.40/0.58          | ~ (l1_pre_topc @ X0)
% 0.40/0.58          | (v2_struct_0 @ X0)
% 0.40/0.58          | ~ (l1_struct_0 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['142', '143'])).
% 0.40/0.58  thf('188', plain,
% 0.40/0.58      (((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.40/0.58         <= (~
% 0.40/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['186', '187'])).
% 0.40/0.58  thf('189', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('190', plain,
% 0.40/0.58      (((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.40/0.58         <= (~
% 0.40/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.58      inference('demod', [status(thm)], ['188', '189'])).
% 0.40/0.58  thf('191', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('192', plain,
% 0.40/0.58      ((~ (l1_struct_0 @ sk_A))
% 0.40/0.58         <= (~
% 0.40/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.58      inference('clc', [status(thm)], ['190', '191'])).
% 0.40/0.58  thf('193', plain,
% 0.40/0.58      ((~ (l1_pre_topc @ sk_A))
% 0.40/0.58         <= (~
% 0.40/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['154', '192'])).
% 0.40/0.58  thf('194', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('195', plain,
% 0.40/0.58      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.40/0.58       ((r3_waybel_9 @ sk_A @ 
% 0.40/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.58      inference('demod', [status(thm)], ['193', '194'])).
% 0.40/0.58  thf('196', plain, ($false),
% 0.40/0.58      inference('sat_resolution*', [status(thm)], ['1', '152', '153', '195'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
