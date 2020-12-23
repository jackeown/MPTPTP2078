%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WFzrDvjfx1

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:48 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  419 (7974 expanded)
%              Number of leaves         :   55 (2483 expanded)
%              Depth                    :   46
%              Number of atoms          : 5527 (153628 expanded)
%              Number of equality atoms :   72 (2272 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

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
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('6',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('7',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('8',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('10',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('11',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('15',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('16',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

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

thf('17',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v1_xboole_0 @ X32 )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 )
      | ( v1_xboole_0 @ X34 )
      | ~ ( v2_waybel_0 @ X34 @ ( k3_yellow_1 @ X32 ) )
      | ~ ( v13_waybel_0 @ X34 @ ( k3_yellow_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X32 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X33 @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('18',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('19',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('20',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('21',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v1_xboole_0 @ X32 )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 )
      | ( v1_xboole_0 @ X34 )
      | ~ ( v2_waybel_0 @ X34 @ ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) )
      | ~ ( v13_waybel_0 @ X34 @ ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X33 @ X32 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( v13_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    v13_waybel_0 @ sk_B_3 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('25',plain,(
    v13_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    v2_waybel_0 @ sk_B_3 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('28',plain,(
    v2_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['22','25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_3 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['11','33'])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
    | ( v1_xboole_0 @ sk_B_3 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
    | ( v1_xboole_0 @ sk_B_3 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('39',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('40',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('41',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

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

thf('43',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( v1_xboole_0 @ X35 )
      | ~ ( l1_struct_0 @ X36 )
      | ( v2_struct_0 @ X36 )
      | ( v1_xboole_0 @ X37 )
      | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ X35 ) ) )
      | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ X35 ) )
      | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X35 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X36 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('44',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('45',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('46',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('47',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('48',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( v1_xboole_0 @ X35 )
      | ~ ( l1_struct_0 @ X36 )
      | ( v2_struct_0 @ X36 )
      | ( v1_xboole_0 @ X37 )
      | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X35 ) ) ) )
      | ~ ( v2_waybel_0 @ X37 @ ( k3_lattice3 @ ( k1_lattice3 @ X35 ) ) )
      | ~ ( v13_waybel_0 @ X37 @ ( k3_lattice3 @ ( k1_lattice3 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X35 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X36 @ X35 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( v13_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    v13_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('51',plain,(
    v2_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('52',plain,(
    v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('54',plain,(
    v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['41','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_3 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['39','59'])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
    | ( v1_xboole_0 @ sk_B_3 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
    | ( v1_xboole_0 @ sk_B_3 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('65',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('66',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('67',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('69',plain,
    ( ( m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

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

thf('73',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v1_xboole_0 @ X29 )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( v2_waybel_0 @ X31 @ ( k3_yellow_1 @ X29 ) )
      | ~ ( v13_waybel_0 @ X31 @ ( k3_yellow_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X29 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X30 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('74',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('75',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('76',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('77',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v1_xboole_0 @ X29 )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( v2_waybel_0 @ X31 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) )
      | ~ ( v13_waybel_0 @ X31 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X30 @ X29 @ X31 ) @ X30 ) ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('80',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('81',plain,(
    v13_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('82',plain,
    ( ( v13_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v13_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v13_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('87',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('88',plain,(
    v2_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('89',plain,
    ( ( v2_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['78','85','92'])).

thf('94',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_3 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['65','93'])).

thf('95',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_3 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_3 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['99'])).

thf('101',plain,(
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

thf('102',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v4_orders_2 @ X38 )
      | ~ ( v7_waybel_0 @ X38 )
      | ~ ( l1_waybel_0 @ X38 @ X39 )
      | ~ ( r3_waybel_9 @ X39 @ X38 @ X40 )
      | ( r1_waybel_7 @ X39 @ ( k2_yellow19 @ X39 @ X38 ) @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X39 ) )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('103',plain,(
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
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C_1 )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C_1 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['100','106'])).

thf('108',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('109',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

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

thf('110',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( v1_subset_1 @ X41 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X42 ) ) ) )
      | ~ ( v2_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ X42 ) ) )
      | ~ ( v13_waybel_0 @ X41 @ ( k3_yellow_1 @ ( k2_struct_0 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X42 ) ) ) ) )
      | ( X41
        = ( k2_yellow19 @ X42 @ ( k3_yellow19 @ X42 @ ( k2_struct_0 @ X42 ) @ X41 ) ) )
      | ~ ( l1_struct_0 @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('111',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('112',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('113',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('114',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('115',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ~ ( v1_subset_1 @ X41 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X42 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X41 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X42 ) ) ) )
      | ~ ( v13_waybel_0 @ X41 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X42 ) ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X42 ) ) ) ) ) )
      | ( X41
        = ( k2_yellow19 @ X42 @ ( k3_yellow19 @ X42 @ ( k2_struct_0 @ X42 ) @ X41 ) ) )
      | ~ ( l1_struct_0 @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114'])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_3
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['109','115'])).

thf('117',plain,(
    v13_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('118',plain,(
    v2_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('119',plain,(
    v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_3
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) )
    | ( v1_xboole_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B_3 )
    | ( sk_B_3
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v1_xboole_0 @ sk_B_3 )
    | ( sk_B_3
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ~ ( v1_xboole_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_3
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( sk_B_3
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['107','127'])).

thf('129',plain,
    ( ( ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['98','128'])).

thf('130',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['97','129'])).

thf('131',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['63','131'])).

thf('133',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','133'])).

thf('135',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('140',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('141',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('142',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('143',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v1_xboole_0 @ X29 )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( v2_waybel_0 @ X31 @ ( k3_yellow_1 @ X29 ) )
      | ~ ( v13_waybel_0 @ X31 @ ( k3_yellow_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X29 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('144',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('145',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('146',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('147',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v1_xboole_0 @ X29 )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( v2_waybel_0 @ X31 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) )
      | ~ ( v13_waybel_0 @ X31 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X30 @ X29 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['143','144','145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( v13_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['142','147'])).

thf('149',plain,(
    v13_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('150',plain,(
    v2_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_3 )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['141','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['140','152'])).

thf('154',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_3 )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['139','155'])).

thf('157',plain,
    ( ( ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['138','156'])).

thf('158',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','158'])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
   <= ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('163',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['5','163'])).

thf('165',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','165'])).

thf('167',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( v1_xboole_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['170','171'])).

thf('174',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('175',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X7 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('176',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['173','176'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('178',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('179',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1 = X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,
    ( ( sk_C_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['172','179'])).

thf(d10_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( v7_struct_0 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( B = C ) ) ) ) ) )).

thf('181',plain,(
    ! [X26: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X26 ) @ ( u1_struct_0 @ X26 ) )
      | ( v7_struct_0 @ X26 )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d10_struct_0])).

thf('182',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X7 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,
    ( ( ~ ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ ( sk_C @ sk_A ) )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['180','183'])).

thf('185',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['173','176'])).

thf('186',plain,
    ( ( ( v1_xboole_0 @ ( sk_C @ sk_A ) )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('188',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['170','171'])).

thf('189',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('190',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t35_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) )).

thf('191',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m2_connsp_2 @ ( k2_struct_0 @ X19 ) @ X19 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t35_connsp_2])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m2_connsp_2 @ ( k2_struct_0 @ X0 ) @ X0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( m2_connsp_2 @ ( u1_struct_0 @ X0 ) @ X0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['189','192'])).

thf('194',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d1_tex_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( ( v7_struct_0 @ A )
      <=> ? [B: $i] :
            ( ( ( u1_struct_0 @ A )
              = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
            & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('195',plain,(
    ! [X24: $i] :
      ( ~ ( v7_struct_0 @ X24 )
      | ( m1_subset_1 @ ( sk_B_1 @ X24 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf('196',plain,(
    ! [X24: $i] :
      ( ~ ( v7_struct_0 @ X24 )
      | ( ( u1_struct_0 @ X24 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X24 ) @ ( sk_B_1 @ X24 ) ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf(t10_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
              <=> ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) )).

thf('197',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m2_connsp_2 @ X17 @ X16 @ ( k6_domain_1 @ ( u1_struct_0 @ X16 ) @ X15 ) )
      | ( m1_connsp_2 @ X17 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t10_connsp_2])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m2_connsp_2 @ X1 @ X0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_connsp_2 @ X1 @ X0 @ ( sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( m1_connsp_2 @ X1 @ X0 @ ( sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m2_connsp_2 @ X1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( m2_connsp_2 @ X1 @ X0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_connsp_2 @ X1 @ X0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['195','199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_connsp_2 @ X1 @ X0 @ ( sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( m2_connsp_2 @ X1 @ X0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( m2_connsp_2 @ ( u1_struct_0 @ X0 ) @ X0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_connsp_2 @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['194','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_connsp_2 @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['193','202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( v7_struct_0 @ X0 )
      | ( m1_connsp_2 @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ! [X24: $i] :
      ( ~ ( v7_struct_0 @ X24 )
      | ( m1_subset_1 @ ( sk_B_1 @ X24 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf('206',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t6_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( m1_connsp_2 @ B @ A @ C )
               => ( r2_hidden @ C @ B ) ) ) ) ) )).

thf('207',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_connsp_2 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B_1 @ X0 ) )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['205','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B_1 @ X0 ) )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['204','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['211'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,
    ( ( ~ ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['188','214'])).

thf('216',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( ~ ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['215','216','217'])).

thf('219',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('221',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['187','220'])).

thf('222',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('224',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['186','223'])).

thf('225',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','224'])).

thf('226',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,
    ( ( v1_xboole_0 @ ( sk_C @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1 = X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('229',plain,
    ( ( sk_C_1
      = ( sk_C @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X26: $i] :
      ( ( ( sk_B_2 @ X26 )
       != ( sk_C @ X26 ) )
      | ( v7_struct_0 @ X26 )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d10_struct_0])).

thf('231',plain,
    ( ( ( ( sk_B_2 @ sk_A )
       != sk_C_1 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('233',plain,
    ( ( sk_C_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['172','179'])).

thf('234',plain,(
    ! [X26: $i] :
      ( ( m1_subset_1 @ ( sk_B_2 @ X26 ) @ ( u1_struct_0 @ X26 ) )
      | ( v7_struct_0 @ X26 )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d10_struct_0])).

thf('235',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X7 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('236',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,
    ( ( ~ ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ ( sk_B_2 @ sk_A ) )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['233','236'])).

thf('238',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['173','176'])).

thf('239',plain,
    ( ( ( v1_xboole_0 @ ( sk_B_2 @ sk_A ) )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('241',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B_2 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['239','240'])).

thf('242',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( sk_B_2 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['232','241'])).

thf('243',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( v1_xboole_0 @ ( sk_B_2 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['242','243'])).

thf('245',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1 = X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('246',plain,
    ( ( sk_C_1
      = ( sk_B_2 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,
    ( ( ( sk_C_1 != sk_C_1 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['231','246'])).

thf('248',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('250',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['248','249'])).

thf('251',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','250'])).

thf('252',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['251','252'])).

thf('254',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['99'])).

thf('255',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('256',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('257',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('258',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('259',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('260',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
   <= ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ),
    inference(split,[status(esa)],['99'])).

thf('261',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
    | ( v1_xboole_0 @ sk_B_3 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('262',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
    | ( v1_xboole_0 @ sk_B_3 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('263',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('264',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('265',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('266',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('267',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('268',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v1_xboole_0 @ X29 )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( v2_waybel_0 @ X31 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) )
      | ~ ( v13_waybel_0 @ X31 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X30 @ X29 @ X31 ) @ X30 ) ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('269',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['267','268'])).

thf('270',plain,(
    v13_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('271',plain,(
    v2_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('272',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['269','270','271'])).

thf('273',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['266','272'])).

thf('274',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['265','273'])).

thf('275',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['274','275'])).

thf('277',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_3 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['264','276'])).

thf('278',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_3 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['263','277'])).

thf('279',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_3 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['278','279'])).

thf('281',plain,
    ( sk_B_3
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('282',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v4_orders_2 @ X38 )
      | ~ ( v7_waybel_0 @ X38 )
      | ~ ( l1_waybel_0 @ X38 @ X39 )
      | ~ ( r1_waybel_7 @ X39 @ ( k2_yellow19 @ X39 @ X38 ) @ X40 )
      | ( r3_waybel_9 @ X39 @ X38 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X39 ) )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('283',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) ) ),
    inference('sup-',[status(thm)],['281','282'])).

thf('284',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['283','284','285'])).

thf('287',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['280','286'])).

thf('288',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ X0 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['287'])).

thf('289',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['262','288'])).

thf('290',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ X0 )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['289'])).

thf('291',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['261','290'])).

thf('292',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['291'])).

thf('293',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['260','292'])).

thf('294',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['293','294'])).

thf('296',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('297',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['295','296'])).

thf('298',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_3 )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['139','155'])).

thf('299',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['297','298'])).

thf('300',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['299'])).

thf('301',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['259','300'])).

thf('302',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['301','302'])).

thf('304',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,
    ( ( ( v1_xboole_0 @ sk_B_3 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['303','304'])).

thf('306',plain,(
    ~ ( v1_xboole_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['305','306'])).

thf('308',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['258','307'])).

thf('309',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['257','308'])).

thf('310',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['309','310'])).

thf('312',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['309','310'])).

thf('313',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('314',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['312','313'])).

thf('315',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('316',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1 = X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['314','315'])).

thf('317',plain,
    ( ( sk_C_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['311','316'])).

thf('318',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('319',plain,
    ( ( ~ ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ ( sk_C @ sk_A ) )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['317','318'])).

thf('320',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['312','313'])).

thf('321',plain,
    ( ( ( v1_xboole_0 @ ( sk_C @ sk_A ) )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['319','320'])).

thf('322',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('323',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['309','310'])).

thf('324',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('325',plain,
    ( ( ~ ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['323','324'])).

thf('326',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('327',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,
    ( ( ~ ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['325','326','327'])).

thf('329',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['328','329'])).

thf('331',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['322','330'])).

thf('332',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['331','332'])).

thf('334',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['321','333'])).

thf('335',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( sk_C @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['256','334'])).

thf('336',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('337',plain,
    ( ( v1_xboole_0 @ ( sk_C @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['335','336'])).

thf('338',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1 = X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['314','315'])).

thf('339',plain,
    ( ( sk_C_1
      = ( sk_C @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['337','338'])).

thf('340',plain,(
    ! [X26: $i] :
      ( ( ( sk_B_2 @ X26 )
       != ( sk_C @ X26 ) )
      | ( v7_struct_0 @ X26 )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d10_struct_0])).

thf('341',plain,
    ( ( ( ( sk_B_2 @ sk_A )
       != sk_C_1 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['339','340'])).

thf('342',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('343',plain,
    ( ( sk_C_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['311','316'])).

thf('344',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('345',plain,
    ( ( ~ ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ ( sk_B_2 @ sk_A ) )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['343','344'])).

thf('346',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['312','313'])).

thf('347',plain,
    ( ( ( v1_xboole_0 @ ( sk_B_2 @ sk_A ) )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['345','346'])).

thf('348',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['331','332'])).

thf('349',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B_2 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['347','348'])).

thf('350',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( sk_B_2 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['342','349'])).

thf('351',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('352',plain,
    ( ( v1_xboole_0 @ ( sk_B_2 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['350','351'])).

thf('353',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1 = X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['314','315'])).

thf('354',plain,
    ( ( sk_C_1
      = ( sk_B_2 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['352','353'])).

thf('355',plain,
    ( ( ( sk_C_1 != sk_C_1 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['341','354'])).

thf('356',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['355'])).

thf('357',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['331','332'])).

thf('358',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['356','357'])).

thf('359',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['255','358'])).

thf('360',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1 )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['359','360'])).

thf('362',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','253','254','361'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WFzrDvjfx1
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:03:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.49/1.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.49/1.74  % Solved by: fo/fo7.sh
% 1.49/1.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.49/1.74  % done 1729 iterations in 1.274s
% 1.49/1.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.49/1.74  % SZS output start Refutation
% 1.49/1.74  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.49/1.74  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 1.49/1.74  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 1.49/1.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.49/1.74  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 1.49/1.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.49/1.74  thf(sk_B_3_type, type, sk_B_3: $i).
% 1.49/1.74  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 1.49/1.74  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.49/1.74  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.49/1.74  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 1.49/1.74  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 1.49/1.74  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 1.49/1.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.49/1.74  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 1.49/1.74  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 1.49/1.74  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 1.49/1.74  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.49/1.74  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 1.49/1.74  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 1.49/1.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.49/1.74  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.49/1.74  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 1.49/1.74  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.49/1.74  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.49/1.74  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 1.49/1.74  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 1.49/1.74  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.49/1.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.49/1.74  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.49/1.74  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 1.49/1.74  thf(sk_A_type, type, sk_A: $i).
% 1.49/1.74  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 1.49/1.74  thf(sk_C_type, type, sk_C: $i > $i).
% 1.49/1.74  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.49/1.74  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 1.49/1.74  thf(t17_yellow19, conjecture,
% 1.49/1.74    (![A:$i]:
% 1.49/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.49/1.74       ( ![B:$i]:
% 1.49/1.74         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.49/1.74             ( v1_subset_1 @
% 1.49/1.74               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 1.49/1.74             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.49/1.74             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.49/1.74             ( m1_subset_1 @
% 1.49/1.74               B @ 
% 1.49/1.74               ( k1_zfmisc_1 @
% 1.49/1.74                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 1.49/1.74           ( ![C:$i]:
% 1.49/1.74             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.49/1.74               ( ( r3_waybel_9 @
% 1.49/1.74                   A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 1.49/1.74                 ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 1.49/1.74  thf(zf_stmt_0, negated_conjecture,
% 1.49/1.74    (~( ![A:$i]:
% 1.49/1.74        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.49/1.74            ( l1_pre_topc @ A ) ) =>
% 1.49/1.74          ( ![B:$i]:
% 1.49/1.74            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.49/1.74                ( v1_subset_1 @
% 1.49/1.74                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 1.49/1.74                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.49/1.74                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.49/1.74                ( m1_subset_1 @
% 1.49/1.74                  B @ 
% 1.49/1.74                  ( k1_zfmisc_1 @
% 1.49/1.74                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 1.49/1.74              ( ![C:$i]:
% 1.49/1.74                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.49/1.74                  ( ( r3_waybel_9 @
% 1.49/1.74                      A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 1.49/1.74                    ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 1.49/1.74    inference('cnf.neg', [status(esa)], [t17_yellow19])).
% 1.49/1.74  thf('0', plain,
% 1.49/1.74      ((~ (r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)
% 1.49/1.74        | ~ (r3_waybel_9 @ sk_A @ 
% 1.49/1.74             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1))),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('1', plain,
% 1.49/1.74      (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) | 
% 1.49/1.74       ~
% 1.49/1.74       ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1))),
% 1.49/1.74      inference('split', [status(esa)], ['0'])).
% 1.49/1.74  thf(dt_l1_pre_topc, axiom,
% 1.49/1.74    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.49/1.74  thf('2', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('3', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('4', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf(d3_struct_0, axiom,
% 1.49/1.74    (![A:$i]:
% 1.49/1.74     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.49/1.74  thf('5', plain,
% 1.49/1.74      (![X10 : $i]:
% 1.49/1.74         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 1.49/1.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.49/1.74  thf('6', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('7', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('8', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf(dt_k2_subset_1, axiom,
% 1.49/1.74    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.49/1.74  thf('9', plain,
% 1.49/1.74      (![X9 : $i]: (m1_subset_1 @ (k2_subset_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.49/1.74  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.49/1.74  thf('10', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 1.49/1.74      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.49/1.74  thf('11', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 1.49/1.74      inference('demod', [status(thm)], ['9', '10'])).
% 1.49/1.74  thf('12', plain,
% 1.49/1.74      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('13', plain,
% 1.49/1.74      (![X10 : $i]:
% 1.49/1.74         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 1.49/1.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.49/1.74  thf('14', plain,
% 1.49/1.74      ((m1_subset_1 @ sk_B_3 @ 
% 1.49/1.74        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf(d2_yellow_1, axiom,
% 1.49/1.74    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 1.49/1.74  thf('15', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('16', plain,
% 1.49/1.74      ((m1_subset_1 @ sk_B_3 @ 
% 1.49/1.74        (k1_zfmisc_1 @ 
% 1.49/1.74         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.49/1.74      inference('demod', [status(thm)], ['14', '15'])).
% 1.49/1.74  thf(fc4_yellow19, axiom,
% 1.49/1.74    (![A:$i,B:$i,C:$i]:
% 1.49/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 1.49/1.74         ( ~( v1_xboole_0 @ B ) ) & 
% 1.49/1.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.49/1.74         ( ~( v1_xboole_0 @ C ) ) & 
% 1.49/1.74         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 1.49/1.74         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 1.49/1.74         ( m1_subset_1 @
% 1.49/1.74           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 1.49/1.74       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 1.49/1.74         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 1.49/1.74         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 1.49/1.74         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 1.49/1.74  thf('17', plain,
% 1.49/1.74      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 1.49/1.74          | (v1_xboole_0 @ X32)
% 1.49/1.74          | ~ (l1_struct_0 @ X33)
% 1.49/1.74          | (v2_struct_0 @ X33)
% 1.49/1.74          | (v1_xboole_0 @ X34)
% 1.49/1.74          | ~ (v2_waybel_0 @ X34 @ (k3_yellow_1 @ X32))
% 1.49/1.74          | ~ (v13_waybel_0 @ X34 @ (k3_yellow_1 @ X32))
% 1.49/1.74          | ~ (m1_subset_1 @ X34 @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X32))))
% 1.49/1.74          | (v4_orders_2 @ (k3_yellow19 @ X33 @ X32 @ X34)))),
% 1.49/1.74      inference('cnf', [status(esa)], [fc4_yellow19])).
% 1.49/1.74  thf('18', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('19', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('20', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('21', plain,
% 1.49/1.74      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 1.49/1.74          | (v1_xboole_0 @ X32)
% 1.49/1.74          | ~ (l1_struct_0 @ X33)
% 1.49/1.74          | (v2_struct_0 @ X33)
% 1.49/1.74          | (v1_xboole_0 @ X34)
% 1.49/1.74          | ~ (v2_waybel_0 @ X34 @ (k3_lattice3 @ (k1_lattice3 @ X32)))
% 1.49/1.74          | ~ (v13_waybel_0 @ X34 @ (k3_lattice3 @ (k1_lattice3 @ X32)))
% 1.49/1.74          | ~ (m1_subset_1 @ X34 @ 
% 1.49/1.74               (k1_zfmisc_1 @ 
% 1.49/1.74                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X32)))))
% 1.49/1.74          | (v4_orders_2 @ (k3_yellow19 @ X33 @ X32 @ X34)))),
% 1.49/1.74      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 1.49/1.74  thf('22', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | ~ (v13_waybel_0 @ sk_B_3 @ 
% 1.49/1.74               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.49/1.74          | ~ (v2_waybel_0 @ sk_B_3 @ 
% 1.49/1.74               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.49/1.74      inference('sup-', [status(thm)], ['16', '21'])).
% 1.49/1.74  thf('23', plain,
% 1.49/1.74      ((v13_waybel_0 @ sk_B_3 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('24', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('25', plain,
% 1.49/1.74      ((v13_waybel_0 @ sk_B_3 @ 
% 1.49/1.74        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.49/1.74      inference('demod', [status(thm)], ['23', '24'])).
% 1.49/1.74  thf('26', plain,
% 1.49/1.74      ((v2_waybel_0 @ sk_B_3 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('27', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('28', plain,
% 1.49/1.74      ((v2_waybel_0 @ sk_B_3 @ 
% 1.49/1.74        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.49/1.74      inference('demod', [status(thm)], ['26', '27'])).
% 1.49/1.74  thf('29', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.49/1.74      inference('demod', [status(thm)], ['22', '25', '28'])).
% 1.49/1.74  thf('30', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.49/1.74             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.49/1.74          | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['13', '29'])).
% 1.49/1.74  thf('31', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (l1_pre_topc @ sk_A)
% 1.49/1.74          | (v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.49/1.74      inference('sup-', [status(thm)], ['12', '30'])).
% 1.49/1.74  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('33', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.49/1.74      inference('demod', [status(thm)], ['31', '32'])).
% 1.49/1.74  thf('34', plain,
% 1.49/1.74      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74        | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74        | (v2_struct_0 @ sk_A)
% 1.49/1.74        | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['11', '33'])).
% 1.49/1.74  thf('35', plain,
% 1.49/1.74      ((~ (l1_pre_topc @ sk_A)
% 1.49/1.74        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74        | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74        | (v2_struct_0 @ sk_A)
% 1.49/1.74        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['8', '34'])).
% 1.49/1.74  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('37', plain,
% 1.49/1.74      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74        | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74        | (v2_struct_0 @ sk_A)
% 1.49/1.74        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 1.49/1.74      inference('demod', [status(thm)], ['35', '36'])).
% 1.49/1.74  thf('38', plain,
% 1.49/1.74      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('39', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 1.49/1.74      inference('demod', [status(thm)], ['9', '10'])).
% 1.49/1.74  thf('40', plain,
% 1.49/1.74      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('41', plain,
% 1.49/1.74      (![X10 : $i]:
% 1.49/1.74         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 1.49/1.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.49/1.74  thf('42', plain,
% 1.49/1.74      ((m1_subset_1 @ sk_B_3 @ 
% 1.49/1.74        (k1_zfmisc_1 @ 
% 1.49/1.74         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.49/1.74      inference('demod', [status(thm)], ['14', '15'])).
% 1.49/1.74  thf(fc5_yellow19, axiom,
% 1.49/1.74    (![A:$i,B:$i,C:$i]:
% 1.49/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 1.49/1.74         ( ~( v1_xboole_0 @ B ) ) & 
% 1.49/1.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.49/1.74         ( ~( v1_xboole_0 @ C ) ) & 
% 1.49/1.74         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 1.49/1.74         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 1.49/1.74         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 1.49/1.74         ( m1_subset_1 @
% 1.49/1.74           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 1.49/1.74       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 1.49/1.74         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 1.49/1.74         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 1.49/1.74  thf('43', plain,
% 1.49/1.74      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 1.49/1.74          | (v1_xboole_0 @ X35)
% 1.49/1.74          | ~ (l1_struct_0 @ X36)
% 1.49/1.74          | (v2_struct_0 @ X36)
% 1.49/1.74          | (v1_xboole_0 @ X37)
% 1.49/1.74          | ~ (v1_subset_1 @ X37 @ (u1_struct_0 @ (k3_yellow_1 @ X35)))
% 1.49/1.74          | ~ (v2_waybel_0 @ X37 @ (k3_yellow_1 @ X35))
% 1.49/1.74          | ~ (v13_waybel_0 @ X37 @ (k3_yellow_1 @ X35))
% 1.49/1.74          | ~ (m1_subset_1 @ X37 @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X35))))
% 1.49/1.74          | (v7_waybel_0 @ (k3_yellow19 @ X36 @ X35 @ X37)))),
% 1.49/1.74      inference('cnf', [status(esa)], [fc5_yellow19])).
% 1.49/1.74  thf('44', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('45', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('46', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('47', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('48', plain,
% 1.49/1.74      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 1.49/1.74          | (v1_xboole_0 @ X35)
% 1.49/1.74          | ~ (l1_struct_0 @ X36)
% 1.49/1.74          | (v2_struct_0 @ X36)
% 1.49/1.74          | (v1_xboole_0 @ X37)
% 1.49/1.74          | ~ (v1_subset_1 @ X37 @ 
% 1.49/1.74               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X35))))
% 1.49/1.74          | ~ (v2_waybel_0 @ X37 @ (k3_lattice3 @ (k1_lattice3 @ X35)))
% 1.49/1.74          | ~ (v13_waybel_0 @ X37 @ (k3_lattice3 @ (k1_lattice3 @ X35)))
% 1.49/1.74          | ~ (m1_subset_1 @ X37 @ 
% 1.49/1.74               (k1_zfmisc_1 @ 
% 1.49/1.74                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X35)))))
% 1.49/1.74          | (v7_waybel_0 @ (k3_yellow19 @ X36 @ X35 @ X37)))),
% 1.49/1.74      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 1.49/1.74  thf('49', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | ~ (v13_waybel_0 @ sk_B_3 @ 
% 1.49/1.74               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.49/1.74          | ~ (v2_waybel_0 @ sk_B_3 @ 
% 1.49/1.74               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.49/1.74          | ~ (v1_subset_1 @ sk_B_3 @ 
% 1.49/1.74               (u1_struct_0 @ 
% 1.49/1.74                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.49/1.74      inference('sup-', [status(thm)], ['42', '48'])).
% 1.49/1.74  thf('50', plain,
% 1.49/1.74      ((v13_waybel_0 @ sk_B_3 @ 
% 1.49/1.74        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.49/1.74      inference('demod', [status(thm)], ['23', '24'])).
% 1.49/1.74  thf('51', plain,
% 1.49/1.74      ((v2_waybel_0 @ sk_B_3 @ 
% 1.49/1.74        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.49/1.74      inference('demod', [status(thm)], ['26', '27'])).
% 1.49/1.74  thf('52', plain,
% 1.49/1.74      ((v1_subset_1 @ sk_B_3 @ 
% 1.49/1.74        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('53', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('54', plain,
% 1.49/1.74      ((v1_subset_1 @ sk_B_3 @ 
% 1.49/1.74        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 1.49/1.74      inference('demod', [status(thm)], ['52', '53'])).
% 1.49/1.74  thf('55', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.49/1.74      inference('demod', [status(thm)], ['49', '50', '51', '54'])).
% 1.49/1.74  thf('56', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.49/1.74             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.49/1.74          | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['41', '55'])).
% 1.49/1.74  thf('57', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (l1_pre_topc @ sk_A)
% 1.49/1.74          | (v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.49/1.74      inference('sup-', [status(thm)], ['40', '56'])).
% 1.49/1.74  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('59', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.49/1.74      inference('demod', [status(thm)], ['57', '58'])).
% 1.49/1.74  thf('60', plain,
% 1.49/1.74      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74        | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74        | (v2_struct_0 @ sk_A)
% 1.49/1.74        | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['39', '59'])).
% 1.49/1.74  thf('61', plain,
% 1.49/1.74      ((~ (l1_pre_topc @ sk_A)
% 1.49/1.74        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74        | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74        | (v2_struct_0 @ sk_A)
% 1.49/1.74        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['38', '60'])).
% 1.49/1.74  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('63', plain,
% 1.49/1.74      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74        | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74        | (v2_struct_0 @ sk_A)
% 1.49/1.74        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 1.49/1.74      inference('demod', [status(thm)], ['61', '62'])).
% 1.49/1.74  thf('64', plain,
% 1.49/1.74      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('65', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 1.49/1.74      inference('demod', [status(thm)], ['9', '10'])).
% 1.49/1.74  thf('66', plain,
% 1.49/1.74      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('67', plain,
% 1.49/1.74      (![X10 : $i]:
% 1.49/1.74         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 1.49/1.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.49/1.74  thf('68', plain,
% 1.49/1.74      ((m1_subset_1 @ sk_B_3 @ 
% 1.49/1.74        (k1_zfmisc_1 @ 
% 1.49/1.74         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.49/1.74      inference('demod', [status(thm)], ['14', '15'])).
% 1.49/1.74  thf('69', plain,
% 1.49/1.74      (((m1_subset_1 @ sk_B_3 @ 
% 1.49/1.74         (k1_zfmisc_1 @ 
% 1.49/1.74          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 1.49/1.74        | ~ (l1_struct_0 @ sk_A))),
% 1.49/1.74      inference('sup+', [status(thm)], ['67', '68'])).
% 1.49/1.74  thf('70', plain,
% 1.49/1.74      ((~ (l1_pre_topc @ sk_A)
% 1.49/1.74        | (m1_subset_1 @ sk_B_3 @ 
% 1.49/1.74           (k1_zfmisc_1 @ 
% 1.49/1.74            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))))),
% 1.49/1.74      inference('sup-', [status(thm)], ['66', '69'])).
% 1.49/1.74  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('72', plain,
% 1.49/1.74      ((m1_subset_1 @ sk_B_3 @ 
% 1.49/1.74        (k1_zfmisc_1 @ 
% 1.49/1.74         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 1.49/1.74      inference('demod', [status(thm)], ['70', '71'])).
% 1.49/1.74  thf(dt_k3_yellow19, axiom,
% 1.49/1.74    (![A:$i,B:$i,C:$i]:
% 1.49/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 1.49/1.74         ( ~( v1_xboole_0 @ B ) ) & 
% 1.49/1.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.49/1.74         ( ~( v1_xboole_0 @ C ) ) & 
% 1.49/1.74         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 1.49/1.74         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 1.49/1.74         ( m1_subset_1 @
% 1.49/1.74           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 1.49/1.74       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 1.49/1.74         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 1.49/1.74         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 1.49/1.74  thf('73', plain,
% 1.49/1.74      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.49/1.74          | (v1_xboole_0 @ X29)
% 1.49/1.74          | ~ (l1_struct_0 @ X30)
% 1.49/1.74          | (v2_struct_0 @ X30)
% 1.49/1.74          | (v1_xboole_0 @ X31)
% 1.49/1.74          | ~ (v2_waybel_0 @ X31 @ (k3_yellow_1 @ X29))
% 1.49/1.74          | ~ (v13_waybel_0 @ X31 @ (k3_yellow_1 @ X29))
% 1.49/1.74          | ~ (m1_subset_1 @ X31 @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X29))))
% 1.49/1.74          | (l1_waybel_0 @ (k3_yellow19 @ X30 @ X29 @ X31) @ X30))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 1.49/1.74  thf('74', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('75', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('76', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('77', plain,
% 1.49/1.74      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.49/1.74          | (v1_xboole_0 @ X29)
% 1.49/1.74          | ~ (l1_struct_0 @ X30)
% 1.49/1.74          | (v2_struct_0 @ X30)
% 1.49/1.74          | (v1_xboole_0 @ X31)
% 1.49/1.74          | ~ (v2_waybel_0 @ X31 @ (k3_lattice3 @ (k1_lattice3 @ X29)))
% 1.49/1.74          | ~ (v13_waybel_0 @ X31 @ (k3_lattice3 @ (k1_lattice3 @ X29)))
% 1.49/1.74          | ~ (m1_subset_1 @ X31 @ 
% 1.49/1.74               (k1_zfmisc_1 @ 
% 1.49/1.74                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X29)))))
% 1.49/1.74          | (l1_waybel_0 @ (k3_yellow19 @ X30 @ X29 @ X31) @ X30))),
% 1.49/1.74      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 1.49/1.74  thf('78', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.49/1.74           X0)
% 1.49/1.74          | ~ (v13_waybel_0 @ sk_B_3 @ 
% 1.49/1.74               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 1.49/1.74          | ~ (v2_waybel_0 @ sk_B_3 @ 
% 1.49/1.74               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.49/1.74      inference('sup-', [status(thm)], ['72', '77'])).
% 1.49/1.74  thf('79', plain,
% 1.49/1.74      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('80', plain,
% 1.49/1.74      (![X10 : $i]:
% 1.49/1.74         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 1.49/1.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.49/1.74  thf('81', plain,
% 1.49/1.74      ((v13_waybel_0 @ sk_B_3 @ 
% 1.49/1.74        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.49/1.74      inference('demod', [status(thm)], ['23', '24'])).
% 1.49/1.74  thf('82', plain,
% 1.49/1.74      (((v13_waybel_0 @ sk_B_3 @ 
% 1.49/1.74         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 1.49/1.74        | ~ (l1_struct_0 @ sk_A))),
% 1.49/1.74      inference('sup+', [status(thm)], ['80', '81'])).
% 1.49/1.74  thf('83', plain,
% 1.49/1.74      ((~ (l1_pre_topc @ sk_A)
% 1.49/1.74        | (v13_waybel_0 @ sk_B_3 @ 
% 1.49/1.74           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 1.49/1.74      inference('sup-', [status(thm)], ['79', '82'])).
% 1.49/1.74  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('85', plain,
% 1.49/1.74      ((v13_waybel_0 @ sk_B_3 @ 
% 1.49/1.74        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 1.49/1.74      inference('demod', [status(thm)], ['83', '84'])).
% 1.49/1.74  thf('86', plain,
% 1.49/1.74      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('87', plain,
% 1.49/1.74      (![X10 : $i]:
% 1.49/1.74         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 1.49/1.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.49/1.74  thf('88', plain,
% 1.49/1.74      ((v2_waybel_0 @ sk_B_3 @ 
% 1.49/1.74        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.49/1.74      inference('demod', [status(thm)], ['26', '27'])).
% 1.49/1.74  thf('89', plain,
% 1.49/1.74      (((v2_waybel_0 @ sk_B_3 @ 
% 1.49/1.74         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 1.49/1.74        | ~ (l1_struct_0 @ sk_A))),
% 1.49/1.74      inference('sup+', [status(thm)], ['87', '88'])).
% 1.49/1.74  thf('90', plain,
% 1.49/1.74      ((~ (l1_pre_topc @ sk_A)
% 1.49/1.74        | (v2_waybel_0 @ sk_B_3 @ 
% 1.49/1.74           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 1.49/1.74      inference('sup-', [status(thm)], ['86', '89'])).
% 1.49/1.74  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('92', plain,
% 1.49/1.74      ((v2_waybel_0 @ sk_B_3 @ 
% 1.49/1.74        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 1.49/1.74      inference('demod', [status(thm)], ['90', '91'])).
% 1.49/1.74  thf('93', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.49/1.74           X0)
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.49/1.74      inference('demod', [status(thm)], ['78', '85', '92'])).
% 1.49/1.74  thf('94', plain,
% 1.49/1.74      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74        | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74        | (v2_struct_0 @ sk_A)
% 1.49/1.74        | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74        | (l1_waybel_0 @ 
% 1.49/1.74           (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_3) @ sk_A))),
% 1.49/1.74      inference('sup-', [status(thm)], ['65', '93'])).
% 1.49/1.74  thf('95', plain,
% 1.49/1.74      ((~ (l1_pre_topc @ sk_A)
% 1.49/1.74        | (l1_waybel_0 @ 
% 1.49/1.74           (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_3) @ sk_A)
% 1.49/1.74        | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74        | (v2_struct_0 @ sk_A)
% 1.49/1.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['64', '94'])).
% 1.49/1.74  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('97', plain,
% 1.49/1.74      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.49/1.74         sk_A)
% 1.49/1.74        | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74        | (v2_struct_0 @ sk_A)
% 1.49/1.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.49/1.74      inference('demod', [status(thm)], ['95', '96'])).
% 1.49/1.74  thf('98', plain,
% 1.49/1.74      (![X10 : $i]:
% 1.49/1.74         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 1.49/1.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.49/1.74  thf('99', plain,
% 1.49/1.74      (((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)
% 1.49/1.74        | (r3_waybel_9 @ sk_A @ 
% 1.49/1.74           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1))),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('100', plain,
% 1.49/1.74      (((r3_waybel_9 @ sk_A @ 
% 1.49/1.74         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1))
% 1.49/1.74         <= (((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('split', [status(esa)], ['99'])).
% 1.49/1.74  thf('101', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf(t12_yellow19, axiom,
% 1.49/1.74    (![A:$i]:
% 1.49/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.49/1.74       ( ![B:$i]:
% 1.49/1.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 1.49/1.74             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 1.49/1.74           ( ![C:$i]:
% 1.49/1.74             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.49/1.74               ( ( r3_waybel_9 @ A @ B @ C ) <=>
% 1.49/1.74                 ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 1.49/1.74  thf('102', plain,
% 1.49/1.74      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.49/1.74         ((v2_struct_0 @ X38)
% 1.49/1.74          | ~ (v4_orders_2 @ X38)
% 1.49/1.74          | ~ (v7_waybel_0 @ X38)
% 1.49/1.74          | ~ (l1_waybel_0 @ X38 @ X39)
% 1.49/1.74          | ~ (r3_waybel_9 @ X39 @ X38 @ X40)
% 1.49/1.74          | (r1_waybel_7 @ X39 @ (k2_yellow19 @ X39 @ X38) @ X40)
% 1.49/1.74          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X39))
% 1.49/1.74          | ~ (l1_pre_topc @ X39)
% 1.49/1.74          | ~ (v2_pre_topc @ X39)
% 1.49/1.74          | (v2_struct_0 @ X39))),
% 1.49/1.74      inference('cnf', [status(esa)], [t12_yellow19])).
% 1.49/1.74  thf('103', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((v2_struct_0 @ sk_A)
% 1.49/1.74          | ~ (v2_pre_topc @ sk_A)
% 1.49/1.74          | ~ (l1_pre_topc @ sk_A)
% 1.49/1.74          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C_1)
% 1.49/1.74          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C_1)
% 1.49/1.74          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 1.49/1.74          | ~ (v7_waybel_0 @ X0)
% 1.49/1.74          | ~ (v4_orders_2 @ X0)
% 1.49/1.74          | (v2_struct_0 @ X0))),
% 1.49/1.74      inference('sup-', [status(thm)], ['101', '102'])).
% 1.49/1.74  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('106', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((v2_struct_0 @ sk_A)
% 1.49/1.74          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C_1)
% 1.49/1.74          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C_1)
% 1.49/1.74          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 1.49/1.74          | ~ (v7_waybel_0 @ X0)
% 1.49/1.74          | ~ (v4_orders_2 @ X0)
% 1.49/1.74          | (v2_struct_0 @ X0))),
% 1.49/1.74      inference('demod', [status(thm)], ['103', '104', '105'])).
% 1.49/1.74  thf('107', plain,
% 1.49/1.74      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | ~ (v4_orders_2 @ 
% 1.49/1.74              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | ~ (v7_waybel_0 @ 
% 1.49/1.74              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | ~ (l1_waybel_0 @ 
% 1.49/1.74              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_A)
% 1.49/1.74         | (r1_waybel_7 @ sk_A @ 
% 1.49/1.74            (k2_yellow19 @ sk_A @ 
% 1.49/1.74             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3)) @ 
% 1.49/1.74            sk_C_1)
% 1.49/1.74         | (v2_struct_0 @ sk_A)))
% 1.49/1.74         <= (((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['100', '106'])).
% 1.49/1.74  thf('108', plain,
% 1.49/1.74      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('109', plain,
% 1.49/1.74      ((m1_subset_1 @ sk_B_3 @ 
% 1.49/1.74        (k1_zfmisc_1 @ 
% 1.49/1.74         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.49/1.74      inference('demod', [status(thm)], ['14', '15'])).
% 1.49/1.74  thf(t15_yellow19, axiom,
% 1.49/1.74    (![A:$i]:
% 1.49/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.49/1.74       ( ![B:$i]:
% 1.49/1.74         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.49/1.74             ( v1_subset_1 @
% 1.49/1.74               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 1.49/1.74             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.49/1.74             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.49/1.74             ( m1_subset_1 @
% 1.49/1.74               B @ 
% 1.49/1.74               ( k1_zfmisc_1 @
% 1.49/1.74                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 1.49/1.74           ( ( B ) =
% 1.49/1.74             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 1.49/1.74  thf('110', plain,
% 1.49/1.74      (![X41 : $i, X42 : $i]:
% 1.49/1.74         ((v1_xboole_0 @ X41)
% 1.49/1.74          | ~ (v1_subset_1 @ X41 @ 
% 1.49/1.74               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X42))))
% 1.49/1.74          | ~ (v2_waybel_0 @ X41 @ (k3_yellow_1 @ (k2_struct_0 @ X42)))
% 1.49/1.74          | ~ (v13_waybel_0 @ X41 @ (k3_yellow_1 @ (k2_struct_0 @ X42)))
% 1.49/1.74          | ~ (m1_subset_1 @ X41 @ 
% 1.49/1.74               (k1_zfmisc_1 @ 
% 1.49/1.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X42)))))
% 1.49/1.74          | ((X41)
% 1.49/1.74              = (k2_yellow19 @ X42 @ 
% 1.49/1.74                 (k3_yellow19 @ X42 @ (k2_struct_0 @ X42) @ X41)))
% 1.49/1.74          | ~ (l1_struct_0 @ X42)
% 1.49/1.74          | (v2_struct_0 @ X42))),
% 1.49/1.74      inference('cnf', [status(esa)], [t15_yellow19])).
% 1.49/1.74  thf('111', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('112', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('113', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('114', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('115', plain,
% 1.49/1.74      (![X41 : $i, X42 : $i]:
% 1.49/1.74         ((v1_xboole_0 @ X41)
% 1.49/1.74          | ~ (v1_subset_1 @ X41 @ 
% 1.49/1.74               (u1_struct_0 @ 
% 1.49/1.74                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X42)))))
% 1.49/1.74          | ~ (v2_waybel_0 @ X41 @ 
% 1.49/1.74               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X42))))
% 1.49/1.74          | ~ (v13_waybel_0 @ X41 @ 
% 1.49/1.74               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X42))))
% 1.49/1.74          | ~ (m1_subset_1 @ X41 @ 
% 1.49/1.74               (k1_zfmisc_1 @ 
% 1.49/1.74                (u1_struct_0 @ 
% 1.49/1.74                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X42))))))
% 1.49/1.74          | ((X41)
% 1.49/1.74              = (k2_yellow19 @ X42 @ 
% 1.49/1.74                 (k3_yellow19 @ X42 @ (k2_struct_0 @ X42) @ X41)))
% 1.49/1.74          | ~ (l1_struct_0 @ X42)
% 1.49/1.74          | (v2_struct_0 @ X42))),
% 1.49/1.74      inference('demod', [status(thm)], ['110', '111', '112', '113', '114'])).
% 1.49/1.74  thf('116', plain,
% 1.49/1.74      (((v2_struct_0 @ sk_A)
% 1.49/1.74        | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74        | ((sk_B_3)
% 1.49/1.74            = (k2_yellow19 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3)))
% 1.49/1.74        | ~ (v13_waybel_0 @ sk_B_3 @ 
% 1.49/1.74             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.49/1.74        | ~ (v2_waybel_0 @ sk_B_3 @ 
% 1.49/1.74             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.49/1.74        | ~ (v1_subset_1 @ sk_B_3 @ 
% 1.49/1.74             (u1_struct_0 @ 
% 1.49/1.74              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 1.49/1.74        | (v1_xboole_0 @ sk_B_3))),
% 1.49/1.74      inference('sup-', [status(thm)], ['109', '115'])).
% 1.49/1.74  thf('117', plain,
% 1.49/1.74      ((v13_waybel_0 @ sk_B_3 @ 
% 1.49/1.74        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.49/1.74      inference('demod', [status(thm)], ['23', '24'])).
% 1.49/1.74  thf('118', plain,
% 1.49/1.74      ((v2_waybel_0 @ sk_B_3 @ 
% 1.49/1.74        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.49/1.74      inference('demod', [status(thm)], ['26', '27'])).
% 1.49/1.74  thf('119', plain,
% 1.49/1.74      ((v1_subset_1 @ sk_B_3 @ 
% 1.49/1.74        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 1.49/1.74      inference('demod', [status(thm)], ['52', '53'])).
% 1.49/1.74  thf('120', plain,
% 1.49/1.74      (((v2_struct_0 @ sk_A)
% 1.49/1.74        | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74        | ((sk_B_3)
% 1.49/1.74            = (k2_yellow19 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3)))
% 1.49/1.74        | (v1_xboole_0 @ sk_B_3))),
% 1.49/1.74      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 1.49/1.74  thf('121', plain,
% 1.49/1.74      ((~ (l1_pre_topc @ sk_A)
% 1.49/1.74        | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74        | ((sk_B_3)
% 1.49/1.74            = (k2_yellow19 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3)))
% 1.49/1.74        | (v2_struct_0 @ sk_A))),
% 1.49/1.74      inference('sup-', [status(thm)], ['108', '120'])).
% 1.49/1.74  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('123', plain,
% 1.49/1.74      (((v1_xboole_0 @ sk_B_3)
% 1.49/1.74        | ((sk_B_3)
% 1.49/1.74            = (k2_yellow19 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3)))
% 1.49/1.74        | (v2_struct_0 @ sk_A))),
% 1.49/1.74      inference('demod', [status(thm)], ['121', '122'])).
% 1.49/1.74  thf('124', plain, (~ (v1_xboole_0 @ sk_B_3)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('125', plain,
% 1.49/1.74      (((v2_struct_0 @ sk_A)
% 1.49/1.74        | ((sk_B_3)
% 1.49/1.74            = (k2_yellow19 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))))),
% 1.49/1.74      inference('clc', [status(thm)], ['123', '124'])).
% 1.49/1.74  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('127', plain,
% 1.49/1.74      (((sk_B_3)
% 1.49/1.74         = (k2_yellow19 @ sk_A @ 
% 1.49/1.74            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3)))),
% 1.49/1.74      inference('clc', [status(thm)], ['125', '126'])).
% 1.49/1.74  thf('128', plain,
% 1.49/1.74      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | ~ (v4_orders_2 @ 
% 1.49/1.74              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | ~ (v7_waybel_0 @ 
% 1.49/1.74              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | ~ (l1_waybel_0 @ 
% 1.49/1.74              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_A)
% 1.49/1.74         | (r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)
% 1.49/1.74         | (v2_struct_0 @ sk_A)))
% 1.49/1.74         <= (((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('demod', [status(thm)], ['107', '127'])).
% 1.49/1.74  thf('129', plain,
% 1.49/1.74      (((~ (l1_waybel_0 @ 
% 1.49/1.74            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_3) @ sk_A)
% 1.49/1.74         | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)
% 1.49/1.74         | ~ (v7_waybel_0 @ 
% 1.49/1.74              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | ~ (v4_orders_2 @ 
% 1.49/1.74              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))))
% 1.49/1.74         <= (((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['98', '128'])).
% 1.49/1.74  thf('130', plain,
% 1.49/1.74      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | ~ (v4_orders_2 @ 
% 1.49/1.74              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | ~ (v7_waybel_0 @ 
% 1.49/1.74              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | (r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | ~ (l1_struct_0 @ sk_A)))
% 1.49/1.74         <= (((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['97', '129'])).
% 1.49/1.74  thf('131', plain,
% 1.49/1.74      (((~ (l1_struct_0 @ sk_A)
% 1.49/1.74         | (r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)
% 1.49/1.74         | ~ (v7_waybel_0 @ 
% 1.49/1.74              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | ~ (v4_orders_2 @ 
% 1.49/1.74              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.49/1.74         <= (((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('simplify', [status(thm)], ['130'])).
% 1.49/1.74  thf('132', plain,
% 1.49/1.74      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | ~ (v4_orders_2 @ 
% 1.49/1.74              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | (r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)
% 1.49/1.74         | ~ (l1_struct_0 @ sk_A)))
% 1.49/1.74         <= (((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['63', '131'])).
% 1.49/1.74  thf('133', plain,
% 1.49/1.74      (((~ (l1_struct_0 @ sk_A)
% 1.49/1.74         | (r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)
% 1.49/1.74         | ~ (v4_orders_2 @ 
% 1.49/1.74              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 1.49/1.74         <= (((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('simplify', [status(thm)], ['132'])).
% 1.49/1.74  thf('134', plain,
% 1.49/1.74      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | (r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)
% 1.49/1.74         | ~ (l1_struct_0 @ sk_A)))
% 1.49/1.74         <= (((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['37', '133'])).
% 1.49/1.74  thf('135', plain,
% 1.49/1.74      (((~ (l1_struct_0 @ sk_A)
% 1.49/1.74         | (r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)
% 1.49/1.74         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 1.49/1.74         <= (((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('simplify', [status(thm)], ['134'])).
% 1.49/1.74  thf('136', plain,
% 1.49/1.74      (((~ (l1_pre_topc @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | (r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))
% 1.49/1.74         <= (((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['7', '135'])).
% 1.49/1.74  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('138', plain,
% 1.49/1.74      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | (r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))
% 1.49/1.74         <= (((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('demod', [status(thm)], ['136', '137'])).
% 1.49/1.74  thf('139', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 1.49/1.74      inference('demod', [status(thm)], ['9', '10'])).
% 1.49/1.74  thf('140', plain,
% 1.49/1.74      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('141', plain,
% 1.49/1.74      (![X10 : $i]:
% 1.49/1.74         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 1.49/1.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.49/1.74  thf('142', plain,
% 1.49/1.74      ((m1_subset_1 @ sk_B_3 @ 
% 1.49/1.74        (k1_zfmisc_1 @ 
% 1.49/1.74         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.49/1.74      inference('demod', [status(thm)], ['14', '15'])).
% 1.49/1.74  thf('143', plain,
% 1.49/1.74      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.49/1.74          | (v1_xboole_0 @ X29)
% 1.49/1.74          | ~ (l1_struct_0 @ X30)
% 1.49/1.74          | (v2_struct_0 @ X30)
% 1.49/1.74          | (v1_xboole_0 @ X31)
% 1.49/1.74          | ~ (v2_waybel_0 @ X31 @ (k3_yellow_1 @ X29))
% 1.49/1.74          | ~ (v13_waybel_0 @ X31 @ (k3_yellow_1 @ X29))
% 1.49/1.74          | ~ (m1_subset_1 @ X31 @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X29))))
% 1.49/1.74          | ~ (v2_struct_0 @ (k3_yellow19 @ X30 @ X29 @ X31)))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 1.49/1.74  thf('144', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('145', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('146', plain,
% 1.49/1.74      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.49/1.74  thf('147', plain,
% 1.49/1.74      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.49/1.74          | (v1_xboole_0 @ X29)
% 1.49/1.74          | ~ (l1_struct_0 @ X30)
% 1.49/1.74          | (v2_struct_0 @ X30)
% 1.49/1.74          | (v1_xboole_0 @ X31)
% 1.49/1.74          | ~ (v2_waybel_0 @ X31 @ (k3_lattice3 @ (k1_lattice3 @ X29)))
% 1.49/1.74          | ~ (v13_waybel_0 @ X31 @ (k3_lattice3 @ (k1_lattice3 @ X29)))
% 1.49/1.74          | ~ (m1_subset_1 @ X31 @ 
% 1.49/1.74               (k1_zfmisc_1 @ 
% 1.49/1.74                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X29)))))
% 1.49/1.74          | ~ (v2_struct_0 @ (k3_yellow19 @ X30 @ X29 @ X31)))),
% 1.49/1.74      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 1.49/1.74  thf('148', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | ~ (v13_waybel_0 @ sk_B_3 @ 
% 1.49/1.74               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.49/1.74          | ~ (v2_waybel_0 @ sk_B_3 @ 
% 1.49/1.74               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.49/1.74      inference('sup-', [status(thm)], ['142', '147'])).
% 1.49/1.74  thf('149', plain,
% 1.49/1.74      ((v13_waybel_0 @ sk_B_3 @ 
% 1.49/1.74        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.49/1.74      inference('demod', [status(thm)], ['23', '24'])).
% 1.49/1.74  thf('150', plain,
% 1.49/1.74      ((v2_waybel_0 @ sk_B_3 @ 
% 1.49/1.74        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.49/1.74      inference('demod', [status(thm)], ['26', '27'])).
% 1.49/1.74  thf('151', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.49/1.74      inference('demod', [status(thm)], ['148', '149', '150'])).
% 1.49/1.74  thf('152', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.49/1.74             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.49/1.74          | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['141', '151'])).
% 1.49/1.74  thf('153', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (l1_pre_topc @ sk_A)
% 1.49/1.74          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.49/1.74      inference('sup-', [status(thm)], ['140', '152'])).
% 1.49/1.74  thf('154', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('155', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.49/1.74      inference('demod', [status(thm)], ['153', '154'])).
% 1.49/1.74  thf('156', plain,
% 1.49/1.74      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74        | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74        | (v2_struct_0 @ sk_A)
% 1.49/1.74        | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['139', '155'])).
% 1.49/1.74  thf('157', plain,
% 1.49/1.74      ((((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)
% 1.49/1.74         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 1.49/1.74         <= (((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['138', '156'])).
% 1.49/1.74  thf('158', plain,
% 1.49/1.74      (((~ (l1_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74         | (r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))
% 1.49/1.74         <= (((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('simplify', [status(thm)], ['157'])).
% 1.49/1.74  thf('159', plain,
% 1.49/1.74      (((~ (l1_pre_topc @ sk_A)
% 1.49/1.74         | (r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)
% 1.49/1.74         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 1.49/1.74         <= (((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['6', '158'])).
% 1.49/1.74  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('161', plain,
% 1.49/1.74      ((((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)
% 1.49/1.74         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 1.49/1.74         <= (((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('demod', [status(thm)], ['159', '160'])).
% 1.49/1.74  thf('162', plain,
% 1.49/1.74      ((~ (r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('split', [status(esa)], ['0'])).
% 1.49/1.74  thf('163', plain,
% 1.49/1.74      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['161', '162'])).
% 1.49/1.74  thf('164', plain,
% 1.49/1.74      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74         | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v2_struct_0 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup+', [status(thm)], ['5', '163'])).
% 1.49/1.74  thf('165', plain,
% 1.49/1.74      ((((v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('simplify', [status(thm)], ['164'])).
% 1.49/1.74  thf('166', plain,
% 1.49/1.74      (((~ (l1_pre_topc @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v2_struct_0 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['4', '165'])).
% 1.49/1.74  thf('167', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('168', plain,
% 1.49/1.74      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v2_struct_0 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('demod', [status(thm)], ['166', '167'])).
% 1.49/1.74  thf('169', plain, (~ (v1_xboole_0 @ sk_B_3)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('170', plain,
% 1.49/1.74      ((((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('clc', [status(thm)], ['168', '169'])).
% 1.49/1.74  thf('171', plain, (~ (v2_struct_0 @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('172', plain,
% 1.49/1.74      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('clc', [status(thm)], ['170', '171'])).
% 1.49/1.74  thf('173', plain,
% 1.49/1.74      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('clc', [status(thm)], ['170', '171'])).
% 1.49/1.74  thf('174', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf(d2_subset_1, axiom,
% 1.49/1.74    (![A:$i,B:$i]:
% 1.49/1.74     ( ( ( v1_xboole_0 @ A ) =>
% 1.49/1.74         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.49/1.74       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.49/1.74         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.49/1.74  thf('175', plain,
% 1.49/1.74      (![X6 : $i, X7 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ X7 @ X6) | (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X6))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.49/1.74  thf('176', plain,
% 1.49/1.74      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_C_1))),
% 1.49/1.74      inference('sup-', [status(thm)], ['174', '175'])).
% 1.49/1.74  thf('177', plain,
% 1.49/1.74      (((v1_xboole_0 @ sk_C_1))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['173', '176'])).
% 1.49/1.74  thf(t8_boole, axiom,
% 1.49/1.74    (![A:$i,B:$i]:
% 1.49/1.74     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.49/1.74  thf('178', plain,
% 1.49/1.74      (![X3 : $i, X4 : $i]:
% 1.49/1.74         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 1.49/1.74      inference('cnf', [status(esa)], [t8_boole])).
% 1.49/1.74  thf('179', plain,
% 1.49/1.74      ((![X0 : $i]: (((sk_C_1) = (X0)) | ~ (v1_xboole_0 @ X0)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['177', '178'])).
% 1.49/1.74  thf('180', plain,
% 1.49/1.74      ((((sk_C_1) = (u1_struct_0 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['172', '179'])).
% 1.49/1.74  thf(d10_struct_0, axiom,
% 1.49/1.74    (![A:$i]:
% 1.49/1.74     ( ( l1_struct_0 @ A ) =>
% 1.49/1.74       ( ( v7_struct_0 @ A ) <=>
% 1.49/1.74         ( ![B:$i]:
% 1.49/1.74           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.49/1.74             ( ![C:$i]:
% 1.49/1.74               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) => ( ( B ) = ( C ) ) ) ) ) ) ) ))).
% 1.49/1.74  thf('181', plain,
% 1.49/1.74      (![X26 : $i]:
% 1.49/1.74         ((m1_subset_1 @ (sk_C @ X26) @ (u1_struct_0 @ X26))
% 1.49/1.74          | (v7_struct_0 @ X26)
% 1.49/1.74          | ~ (l1_struct_0 @ X26))),
% 1.49/1.74      inference('cnf', [status(esa)], [d10_struct_0])).
% 1.49/1.74  thf('182', plain,
% 1.49/1.74      (![X6 : $i, X7 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ X7 @ X6) | (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X6))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.49/1.74  thf('183', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v7_struct_0 @ X0)
% 1.49/1.74          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.49/1.74          | (v1_xboole_0 @ (sk_C @ X0)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['181', '182'])).
% 1.49/1.74  thf('184', plain,
% 1.49/1.74      (((~ (v1_xboole_0 @ sk_C_1)
% 1.49/1.74         | (v1_xboole_0 @ (sk_C @ sk_A))
% 1.49/1.74         | (v7_struct_0 @ sk_A)
% 1.49/1.74         | ~ (l1_struct_0 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['180', '183'])).
% 1.49/1.74  thf('185', plain,
% 1.49/1.74      (((v1_xboole_0 @ sk_C_1))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['173', '176'])).
% 1.49/1.74  thf('186', plain,
% 1.49/1.74      ((((v1_xboole_0 @ (sk_C @ sk_A))
% 1.49/1.74         | (v7_struct_0 @ sk_A)
% 1.49/1.74         | ~ (l1_struct_0 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('demod', [status(thm)], ['184', '185'])).
% 1.49/1.74  thf('187', plain,
% 1.49/1.74      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('188', plain,
% 1.49/1.74      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('clc', [status(thm)], ['170', '171'])).
% 1.49/1.74  thf('189', plain,
% 1.49/1.74      (![X10 : $i]:
% 1.49/1.74         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 1.49/1.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.49/1.74  thf('190', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 1.49/1.74      inference('demod', [status(thm)], ['9', '10'])).
% 1.49/1.74  thf(t35_connsp_2, axiom,
% 1.49/1.74    (![A:$i]:
% 1.49/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.49/1.74       ( ![B:$i]:
% 1.49/1.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.49/1.74           ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ))).
% 1.49/1.74  thf('191', plain,
% 1.49/1.74      (![X18 : $i, X19 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.49/1.74          | (m2_connsp_2 @ (k2_struct_0 @ X19) @ X19 @ X18)
% 1.49/1.74          | ~ (l1_pre_topc @ X19)
% 1.49/1.74          | ~ (v2_pre_topc @ X19)
% 1.49/1.74          | (v2_struct_0 @ X19))),
% 1.49/1.74      inference('cnf', [status(esa)], [t35_connsp_2])).
% 1.49/1.74  thf('192', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((v2_struct_0 @ X0)
% 1.49/1.74          | ~ (v2_pre_topc @ X0)
% 1.49/1.74          | ~ (l1_pre_topc @ X0)
% 1.49/1.74          | (m2_connsp_2 @ (k2_struct_0 @ X0) @ X0 @ (u1_struct_0 @ X0)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['190', '191'])).
% 1.49/1.74  thf('193', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((m2_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ (u1_struct_0 @ X0))
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_pre_topc @ X0)
% 1.49/1.74          | ~ (v2_pre_topc @ X0)
% 1.49/1.74          | (v2_struct_0 @ X0))),
% 1.49/1.74      inference('sup+', [status(thm)], ['189', '192'])).
% 1.49/1.74  thf('194', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 1.49/1.74      inference('demod', [status(thm)], ['9', '10'])).
% 1.49/1.74  thf(d1_tex_1, axiom,
% 1.49/1.74    (![A:$i]:
% 1.49/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.49/1.74       ( ( v7_struct_0 @ A ) <=>
% 1.49/1.74         ( ?[B:$i]:
% 1.49/1.74           ( ( ( u1_struct_0 @ A ) = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) & 
% 1.49/1.74             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.49/1.74  thf('195', plain,
% 1.49/1.74      (![X24 : $i]:
% 1.49/1.74         (~ (v7_struct_0 @ X24)
% 1.49/1.74          | (m1_subset_1 @ (sk_B_1 @ X24) @ (u1_struct_0 @ X24))
% 1.49/1.74          | ~ (l1_struct_0 @ X24)
% 1.49/1.74          | (v2_struct_0 @ X24))),
% 1.49/1.74      inference('cnf', [status(esa)], [d1_tex_1])).
% 1.49/1.74  thf('196', plain,
% 1.49/1.74      (![X24 : $i]:
% 1.49/1.74         (~ (v7_struct_0 @ X24)
% 1.49/1.74          | ((u1_struct_0 @ X24)
% 1.49/1.74              = (k6_domain_1 @ (u1_struct_0 @ X24) @ (sk_B_1 @ X24)))
% 1.49/1.74          | ~ (l1_struct_0 @ X24)
% 1.49/1.74          | (v2_struct_0 @ X24))),
% 1.49/1.74      inference('cnf', [status(esa)], [d1_tex_1])).
% 1.49/1.74  thf(t10_connsp_2, axiom,
% 1.49/1.74    (![A:$i]:
% 1.49/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.49/1.74       ( ![B:$i]:
% 1.49/1.74         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.49/1.74           ( ![C:$i]:
% 1.49/1.74             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.49/1.74               ( ( m2_connsp_2 @
% 1.49/1.74                   C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 1.49/1.74                 ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 1.49/1.74  thf('197', plain,
% 1.49/1.74      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 1.49/1.74          | ~ (m2_connsp_2 @ X17 @ X16 @ 
% 1.49/1.74               (k6_domain_1 @ (u1_struct_0 @ X16) @ X15))
% 1.49/1.74          | (m1_connsp_2 @ X17 @ X16 @ X15)
% 1.49/1.74          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.49/1.74          | ~ (l1_pre_topc @ X16)
% 1.49/1.74          | ~ (v2_pre_topc @ X16)
% 1.49/1.74          | (v2_struct_0 @ X16))),
% 1.49/1.74      inference('cnf', [status(esa)], [t10_connsp_2])).
% 1.49/1.74  thf('198', plain,
% 1.49/1.74      (![X0 : $i, X1 : $i]:
% 1.49/1.74         (~ (m2_connsp_2 @ X1 @ X0 @ (u1_struct_0 @ X0))
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | ~ (v7_struct_0 @ X0)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (v2_pre_topc @ X0)
% 1.49/1.74          | ~ (l1_pre_topc @ X0)
% 1.49/1.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.49/1.74          | (m1_connsp_2 @ X1 @ X0 @ (sk_B_1 @ X0))
% 1.49/1.74          | ~ (m1_subset_1 @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['196', '197'])).
% 1.49/1.74  thf('199', plain,
% 1.49/1.74      (![X0 : $i, X1 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0))
% 1.49/1.74          | (m1_connsp_2 @ X1 @ X0 @ (sk_B_1 @ X0))
% 1.49/1.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.49/1.74          | ~ (l1_pre_topc @ X0)
% 1.49/1.74          | ~ (v2_pre_topc @ X0)
% 1.49/1.74          | ~ (v7_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (m2_connsp_2 @ X1 @ X0 @ (u1_struct_0 @ X0)))),
% 1.49/1.74      inference('simplify', [status(thm)], ['198'])).
% 1.49/1.74  thf('200', plain,
% 1.49/1.74      (![X0 : $i, X1 : $i]:
% 1.49/1.74         ((v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | ~ (v7_struct_0 @ X0)
% 1.49/1.74          | ~ (m2_connsp_2 @ X1 @ X0 @ (u1_struct_0 @ X0))
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | ~ (v7_struct_0 @ X0)
% 1.49/1.74          | ~ (v2_pre_topc @ X0)
% 1.49/1.74          | ~ (l1_pre_topc @ X0)
% 1.49/1.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.49/1.74          | (m1_connsp_2 @ X1 @ X0 @ (sk_B_1 @ X0)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['195', '199'])).
% 1.49/1.74  thf('201', plain,
% 1.49/1.74      (![X0 : $i, X1 : $i]:
% 1.49/1.74         ((m1_connsp_2 @ X1 @ X0 @ (sk_B_1 @ X0))
% 1.49/1.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.49/1.74          | ~ (l1_pre_topc @ X0)
% 1.49/1.74          | ~ (v2_pre_topc @ X0)
% 1.49/1.74          | ~ (m2_connsp_2 @ X1 @ X0 @ (u1_struct_0 @ X0))
% 1.49/1.74          | ~ (v7_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v2_struct_0 @ X0))),
% 1.49/1.74      inference('simplify', [status(thm)], ['200'])).
% 1.49/1.74  thf('202', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | ~ (v7_struct_0 @ X0)
% 1.49/1.74          | ~ (m2_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ (u1_struct_0 @ X0))
% 1.49/1.74          | ~ (v2_pre_topc @ X0)
% 1.49/1.74          | ~ (l1_pre_topc @ X0)
% 1.49/1.74          | (m1_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ (sk_B_1 @ X0)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['194', '201'])).
% 1.49/1.74  thf('203', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((v2_struct_0 @ X0)
% 1.49/1.74          | ~ (v2_pre_topc @ X0)
% 1.49/1.74          | ~ (l1_pre_topc @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (m1_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ (sk_B_1 @ X0))
% 1.49/1.74          | ~ (l1_pre_topc @ X0)
% 1.49/1.74          | ~ (v2_pre_topc @ X0)
% 1.49/1.74          | ~ (v7_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v2_struct_0 @ X0))),
% 1.49/1.74      inference('sup-', [status(thm)], ['193', '202'])).
% 1.49/1.74  thf('204', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (v7_struct_0 @ X0)
% 1.49/1.74          | (m1_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ (sk_B_1 @ X0))
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_pre_topc @ X0)
% 1.49/1.74          | ~ (v2_pre_topc @ X0)
% 1.49/1.74          | (v2_struct_0 @ X0))),
% 1.49/1.74      inference('simplify', [status(thm)], ['203'])).
% 1.49/1.74  thf('205', plain,
% 1.49/1.74      (![X24 : $i]:
% 1.49/1.74         (~ (v7_struct_0 @ X24)
% 1.49/1.74          | (m1_subset_1 @ (sk_B_1 @ X24) @ (u1_struct_0 @ X24))
% 1.49/1.74          | ~ (l1_struct_0 @ X24)
% 1.49/1.74          | (v2_struct_0 @ X24))),
% 1.49/1.74      inference('cnf', [status(esa)], [d1_tex_1])).
% 1.49/1.74  thf('206', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 1.49/1.74      inference('demod', [status(thm)], ['9', '10'])).
% 1.49/1.74  thf(t6_connsp_2, axiom,
% 1.49/1.74    (![A:$i]:
% 1.49/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.49/1.74       ( ![B:$i]:
% 1.49/1.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.49/1.74           ( ![C:$i]:
% 1.49/1.74             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.49/1.74               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.49/1.74  thf('207', plain,
% 1.49/1.74      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.49/1.74          | ~ (m1_connsp_2 @ X20 @ X21 @ X22)
% 1.49/1.74          | (r2_hidden @ X22 @ X20)
% 1.49/1.74          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 1.49/1.74          | ~ (l1_pre_topc @ X21)
% 1.49/1.74          | ~ (v2_pre_topc @ X21)
% 1.49/1.74          | (v2_struct_0 @ X21))),
% 1.49/1.74      inference('cnf', [status(esa)], [t6_connsp_2])).
% 1.49/1.74  thf('208', plain,
% 1.49/1.74      (![X0 : $i, X1 : $i]:
% 1.49/1.74         ((v2_struct_0 @ X0)
% 1.49/1.74          | ~ (v2_pre_topc @ X0)
% 1.49/1.74          | ~ (l1_pre_topc @ X0)
% 1.49/1.74          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 1.49/1.74          | (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 1.49/1.74          | ~ (m1_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ X1))),
% 1.49/1.74      inference('sup-', [status(thm)], ['206', '207'])).
% 1.49/1.74  thf('209', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | ~ (v7_struct_0 @ X0)
% 1.49/1.74          | ~ (m1_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ (sk_B_1 @ X0))
% 1.49/1.74          | (r2_hidden @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0))
% 1.49/1.74          | ~ (l1_pre_topc @ X0)
% 1.49/1.74          | ~ (v2_pre_topc @ X0)
% 1.49/1.74          | (v2_struct_0 @ X0))),
% 1.49/1.74      inference('sup-', [status(thm)], ['205', '208'])).
% 1.49/1.74  thf('210', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (v2_pre_topc @ X0)
% 1.49/1.74          | ~ (l1_pre_topc @ X0)
% 1.49/1.74          | (r2_hidden @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0))
% 1.49/1.74          | ~ (m1_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ (sk_B_1 @ X0))
% 1.49/1.74          | ~ (v7_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v2_struct_0 @ X0))),
% 1.49/1.74      inference('simplify', [status(thm)], ['209'])).
% 1.49/1.74  thf('211', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((v2_struct_0 @ X0)
% 1.49/1.74          | ~ (v2_pre_topc @ X0)
% 1.49/1.74          | ~ (l1_pre_topc @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | ~ (v7_struct_0 @ X0)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | ~ (v7_struct_0 @ X0)
% 1.49/1.74          | (r2_hidden @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0))
% 1.49/1.74          | ~ (l1_pre_topc @ X0)
% 1.49/1.74          | ~ (v2_pre_topc @ X0))),
% 1.49/1.74      inference('sup-', [status(thm)], ['204', '210'])).
% 1.49/1.74  thf('212', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((r2_hidden @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0))
% 1.49/1.74          | ~ (v7_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_pre_topc @ X0)
% 1.49/1.74          | ~ (v2_pre_topc @ X0)
% 1.49/1.74          | (v2_struct_0 @ X0))),
% 1.49/1.74      inference('simplify', [status(thm)], ['211'])).
% 1.49/1.74  thf(d1_xboole_0, axiom,
% 1.49/1.74    (![A:$i]:
% 1.49/1.74     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.49/1.74  thf('213', plain,
% 1.49/1.74      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.49/1.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.49/1.74  thf('214', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((v2_struct_0 @ X0)
% 1.49/1.74          | ~ (v2_pre_topc @ X0)
% 1.49/1.74          | ~ (l1_pre_topc @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | ~ (v7_struct_0 @ X0)
% 1.49/1.74          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['212', '213'])).
% 1.49/1.74  thf('215', plain,
% 1.49/1.74      (((~ (v7_struct_0 @ sk_A)
% 1.49/1.74         | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74         | ~ (l1_pre_topc @ sk_A)
% 1.49/1.74         | ~ (v2_pre_topc @ sk_A)
% 1.49/1.74         | (v2_struct_0 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['188', '214'])).
% 1.49/1.74  thf('216', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('217', plain, ((v2_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('218', plain,
% 1.49/1.74      (((~ (v7_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('demod', [status(thm)], ['215', '216', '217'])).
% 1.49/1.74  thf('219', plain, (~ (v2_struct_0 @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('220', plain,
% 1.49/1.74      (((~ (l1_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('clc', [status(thm)], ['218', '219'])).
% 1.49/1.74  thf('221', plain,
% 1.49/1.74      (((~ (l1_pre_topc @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['187', '220'])).
% 1.49/1.74  thf('222', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('223', plain,
% 1.49/1.74      ((~ (v7_struct_0 @ sk_A))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('demod', [status(thm)], ['221', '222'])).
% 1.49/1.74  thf('224', plain,
% 1.49/1.74      (((~ (l1_struct_0 @ sk_A) | (v1_xboole_0 @ (sk_C @ sk_A))))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('clc', [status(thm)], ['186', '223'])).
% 1.49/1.74  thf('225', plain,
% 1.49/1.74      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (sk_C @ sk_A))))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['3', '224'])).
% 1.49/1.74  thf('226', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('227', plain,
% 1.49/1.74      (((v1_xboole_0 @ (sk_C @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('demod', [status(thm)], ['225', '226'])).
% 1.49/1.74  thf('228', plain,
% 1.49/1.74      ((![X0 : $i]: (((sk_C_1) = (X0)) | ~ (v1_xboole_0 @ X0)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['177', '178'])).
% 1.49/1.74  thf('229', plain,
% 1.49/1.74      ((((sk_C_1) = (sk_C @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['227', '228'])).
% 1.49/1.74  thf('230', plain,
% 1.49/1.74      (![X26 : $i]:
% 1.49/1.74         (((sk_B_2 @ X26) != (sk_C @ X26))
% 1.49/1.74          | (v7_struct_0 @ X26)
% 1.49/1.74          | ~ (l1_struct_0 @ X26))),
% 1.49/1.74      inference('cnf', [status(esa)], [d10_struct_0])).
% 1.49/1.74  thf('231', plain,
% 1.49/1.74      (((((sk_B_2 @ sk_A) != (sk_C_1))
% 1.49/1.74         | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74         | (v7_struct_0 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['229', '230'])).
% 1.49/1.74  thf('232', plain,
% 1.49/1.74      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('233', plain,
% 1.49/1.74      ((((sk_C_1) = (u1_struct_0 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['172', '179'])).
% 1.49/1.74  thf('234', plain,
% 1.49/1.74      (![X26 : $i]:
% 1.49/1.74         ((m1_subset_1 @ (sk_B_2 @ X26) @ (u1_struct_0 @ X26))
% 1.49/1.74          | (v7_struct_0 @ X26)
% 1.49/1.74          | ~ (l1_struct_0 @ X26))),
% 1.49/1.74      inference('cnf', [status(esa)], [d10_struct_0])).
% 1.49/1.74  thf('235', plain,
% 1.49/1.74      (![X6 : $i, X7 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ X7 @ X6) | (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X6))),
% 1.49/1.74      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.49/1.74  thf('236', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v7_struct_0 @ X0)
% 1.49/1.74          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.49/1.74          | (v1_xboole_0 @ (sk_B_2 @ X0)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['234', '235'])).
% 1.49/1.74  thf('237', plain,
% 1.49/1.74      (((~ (v1_xboole_0 @ sk_C_1)
% 1.49/1.74         | (v1_xboole_0 @ (sk_B_2 @ sk_A))
% 1.49/1.74         | (v7_struct_0 @ sk_A)
% 1.49/1.74         | ~ (l1_struct_0 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['233', '236'])).
% 1.49/1.74  thf('238', plain,
% 1.49/1.74      (((v1_xboole_0 @ sk_C_1))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['173', '176'])).
% 1.49/1.74  thf('239', plain,
% 1.49/1.74      ((((v1_xboole_0 @ (sk_B_2 @ sk_A))
% 1.49/1.74         | (v7_struct_0 @ sk_A)
% 1.49/1.74         | ~ (l1_struct_0 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('demod', [status(thm)], ['237', '238'])).
% 1.49/1.74  thf('240', plain,
% 1.49/1.74      ((~ (v7_struct_0 @ sk_A))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('demod', [status(thm)], ['221', '222'])).
% 1.49/1.74  thf('241', plain,
% 1.49/1.74      (((~ (l1_struct_0 @ sk_A) | (v1_xboole_0 @ (sk_B_2 @ sk_A))))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('clc', [status(thm)], ['239', '240'])).
% 1.49/1.74  thf('242', plain,
% 1.49/1.74      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (sk_B_2 @ sk_A))))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['232', '241'])).
% 1.49/1.74  thf('243', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('244', plain,
% 1.49/1.74      (((v1_xboole_0 @ (sk_B_2 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('demod', [status(thm)], ['242', '243'])).
% 1.49/1.74  thf('245', plain,
% 1.49/1.74      ((![X0 : $i]: (((sk_C_1) = (X0)) | ~ (v1_xboole_0 @ X0)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['177', '178'])).
% 1.49/1.74  thf('246', plain,
% 1.49/1.74      ((((sk_C_1) = (sk_B_2 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['244', '245'])).
% 1.49/1.74  thf('247', plain,
% 1.49/1.74      (((((sk_C_1) != (sk_C_1)) | ~ (l1_struct_0 @ sk_A) | (v7_struct_0 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('demod', [status(thm)], ['231', '246'])).
% 1.49/1.74  thf('248', plain,
% 1.49/1.74      ((((v7_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('simplify', [status(thm)], ['247'])).
% 1.49/1.74  thf('249', plain,
% 1.49/1.74      ((~ (v7_struct_0 @ sk_A))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('demod', [status(thm)], ['221', '222'])).
% 1.49/1.74  thf('250', plain,
% 1.49/1.74      ((~ (l1_struct_0 @ sk_A))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('clc', [status(thm)], ['248', '249'])).
% 1.49/1.74  thf('251', plain,
% 1.49/1.74      ((~ (l1_pre_topc @ sk_A))
% 1.49/1.74         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) & 
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['2', '250'])).
% 1.49/1.74  thf('252', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('253', plain,
% 1.49/1.74      (((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) | 
% 1.49/1.74       ~
% 1.49/1.74       ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1))),
% 1.49/1.74      inference('demod', [status(thm)], ['251', '252'])).
% 1.49/1.74  thf('254', plain,
% 1.49/1.74      (((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) | 
% 1.49/1.74       ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1))),
% 1.49/1.74      inference('split', [status(esa)], ['99'])).
% 1.49/1.74  thf('255', plain,
% 1.49/1.74      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('256', plain,
% 1.49/1.74      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('257', plain,
% 1.49/1.74      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('258', plain,
% 1.49/1.74      (![X10 : $i]:
% 1.49/1.74         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 1.49/1.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.49/1.74  thf('259', plain,
% 1.49/1.74      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('260', plain,
% 1.49/1.74      (((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1))
% 1.49/1.74         <= (((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('split', [status(esa)], ['99'])).
% 1.49/1.74  thf('261', plain,
% 1.49/1.74      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74        | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74        | (v2_struct_0 @ sk_A)
% 1.49/1.74        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 1.49/1.74      inference('demod', [status(thm)], ['35', '36'])).
% 1.49/1.74  thf('262', plain,
% 1.49/1.74      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74        | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74        | (v2_struct_0 @ sk_A)
% 1.49/1.74        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 1.49/1.74      inference('demod', [status(thm)], ['61', '62'])).
% 1.49/1.74  thf('263', plain,
% 1.49/1.74      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('264', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 1.49/1.74      inference('demod', [status(thm)], ['9', '10'])).
% 1.49/1.74  thf('265', plain,
% 1.49/1.74      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('266', plain,
% 1.49/1.74      (![X10 : $i]:
% 1.49/1.74         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 1.49/1.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.49/1.74  thf('267', plain,
% 1.49/1.74      ((m1_subset_1 @ sk_B_3 @ 
% 1.49/1.74        (k1_zfmisc_1 @ 
% 1.49/1.74         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.49/1.74      inference('demod', [status(thm)], ['14', '15'])).
% 1.49/1.74  thf('268', plain,
% 1.49/1.74      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.49/1.74          | (v1_xboole_0 @ X29)
% 1.49/1.74          | ~ (l1_struct_0 @ X30)
% 1.49/1.74          | (v2_struct_0 @ X30)
% 1.49/1.74          | (v1_xboole_0 @ X31)
% 1.49/1.74          | ~ (v2_waybel_0 @ X31 @ (k3_lattice3 @ (k1_lattice3 @ X29)))
% 1.49/1.74          | ~ (v13_waybel_0 @ X31 @ (k3_lattice3 @ (k1_lattice3 @ X29)))
% 1.49/1.74          | ~ (m1_subset_1 @ X31 @ 
% 1.49/1.74               (k1_zfmisc_1 @ 
% 1.49/1.74                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X29)))))
% 1.49/1.74          | (l1_waybel_0 @ (k3_yellow19 @ X30 @ X29 @ X31) @ X30))),
% 1.49/1.74      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 1.49/1.74  thf('269', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.49/1.74           X0)
% 1.49/1.74          | ~ (v13_waybel_0 @ sk_B_3 @ 
% 1.49/1.74               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.49/1.74          | ~ (v2_waybel_0 @ sk_B_3 @ 
% 1.49/1.74               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.49/1.74      inference('sup-', [status(thm)], ['267', '268'])).
% 1.49/1.74  thf('270', plain,
% 1.49/1.74      ((v13_waybel_0 @ sk_B_3 @ 
% 1.49/1.74        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.49/1.74      inference('demod', [status(thm)], ['23', '24'])).
% 1.49/1.74  thf('271', plain,
% 1.49/1.74      ((v2_waybel_0 @ sk_B_3 @ 
% 1.49/1.74        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.49/1.74      inference('demod', [status(thm)], ['26', '27'])).
% 1.49/1.74  thf('272', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.49/1.74           X0)
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.49/1.74      inference('demod', [status(thm)], ['269', '270', '271'])).
% 1.49/1.74  thf('273', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.49/1.74             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.49/1.74          | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (l1_waybel_0 @ 
% 1.49/1.74             (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3) @ X0))),
% 1.49/1.74      inference('sup-', [status(thm)], ['266', '272'])).
% 1.49/1.74  thf('274', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (l1_pre_topc @ sk_A)
% 1.49/1.74          | (l1_waybel_0 @ 
% 1.49/1.74             (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3) @ X0)
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.49/1.74      inference('sup-', [status(thm)], ['265', '273'])).
% 1.49/1.74  thf('275', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('276', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.49/1.74           X0)
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.49/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.49/1.74      inference('demod', [status(thm)], ['274', '275'])).
% 1.49/1.74  thf('277', plain,
% 1.49/1.74      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74        | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74        | (v2_struct_0 @ sk_A)
% 1.49/1.74        | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74        | (l1_waybel_0 @ 
% 1.49/1.74           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_A))),
% 1.49/1.74      inference('sup-', [status(thm)], ['264', '276'])).
% 1.49/1.74  thf('278', plain,
% 1.49/1.74      ((~ (l1_pre_topc @ sk_A)
% 1.49/1.74        | (l1_waybel_0 @ 
% 1.49/1.74           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_A)
% 1.49/1.74        | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74        | (v2_struct_0 @ sk_A)
% 1.49/1.74        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['263', '277'])).
% 1.49/1.74  thf('279', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('280', plain,
% 1.49/1.74      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.49/1.74         sk_A)
% 1.49/1.74        | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74        | (v2_struct_0 @ sk_A)
% 1.49/1.74        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 1.49/1.74      inference('demod', [status(thm)], ['278', '279'])).
% 1.49/1.74  thf('281', plain,
% 1.49/1.74      (((sk_B_3)
% 1.49/1.74         = (k2_yellow19 @ sk_A @ 
% 1.49/1.74            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3)))),
% 1.49/1.74      inference('clc', [status(thm)], ['125', '126'])).
% 1.49/1.74  thf('282', plain,
% 1.49/1.74      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.49/1.74         ((v2_struct_0 @ X38)
% 1.49/1.74          | ~ (v4_orders_2 @ X38)
% 1.49/1.74          | ~ (v7_waybel_0 @ X38)
% 1.49/1.74          | ~ (l1_waybel_0 @ X38 @ X39)
% 1.49/1.74          | ~ (r1_waybel_7 @ X39 @ (k2_yellow19 @ X39 @ X38) @ X40)
% 1.49/1.74          | (r3_waybel_9 @ X39 @ X38 @ X40)
% 1.49/1.74          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X39))
% 1.49/1.74          | ~ (l1_pre_topc @ X39)
% 1.49/1.74          | ~ (v2_pre_topc @ X39)
% 1.49/1.74          | (v2_struct_0 @ X39))),
% 1.49/1.74      inference('cnf', [status(esa)], [t12_yellow19])).
% 1.49/1.74  thf('283', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (r1_waybel_7 @ sk_A @ sk_B_3 @ X0)
% 1.49/1.74          | (v2_struct_0 @ sk_A)
% 1.49/1.74          | ~ (v2_pre_topc @ sk_A)
% 1.49/1.74          | ~ (l1_pre_topc @ sk_A)
% 1.49/1.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74          | (r3_waybel_9 @ sk_A @ 
% 1.49/1.74             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ X0)
% 1.49/1.74          | ~ (l1_waybel_0 @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_A)
% 1.49/1.74          | ~ (v7_waybel_0 @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | ~ (v4_orders_2 @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['281', '282'])).
% 1.49/1.74  thf('284', plain, ((v2_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('285', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('286', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (r1_waybel_7 @ sk_A @ sk_B_3 @ X0)
% 1.49/1.74          | (v2_struct_0 @ sk_A)
% 1.49/1.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74          | (r3_waybel_9 @ sk_A @ 
% 1.49/1.74             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ X0)
% 1.49/1.74          | ~ (l1_waybel_0 @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_A)
% 1.49/1.74          | ~ (v7_waybel_0 @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | ~ (v4_orders_2 @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3)))),
% 1.49/1.74      inference('demod', [status(thm)], ['283', '284', '285'])).
% 1.49/1.74  thf('287', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | (v2_struct_0 @ sk_A)
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | ~ (v4_orders_2 @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | ~ (v7_waybel_0 @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | (r3_waybel_9 @ sk_A @ 
% 1.49/1.74             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ X0)
% 1.49/1.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74          | (v2_struct_0 @ sk_A)
% 1.49/1.74          | ~ (r1_waybel_7 @ sk_A @ sk_B_3 @ X0))),
% 1.49/1.74      inference('sup-', [status(thm)], ['280', '286'])).
% 1.49/1.74  thf('288', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (r1_waybel_7 @ sk_A @ sk_B_3 @ X0)
% 1.49/1.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74          | (r3_waybel_9 @ sk_A @ 
% 1.49/1.74             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ X0)
% 1.49/1.74          | ~ (v7_waybel_0 @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | ~ (v4_orders_2 @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ sk_A)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 1.49/1.74      inference('simplify', [status(thm)], ['287'])).
% 1.49/1.74  thf('289', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | (v2_struct_0 @ sk_A)
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | (v2_struct_0 @ sk_A)
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | ~ (v4_orders_2 @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | (r3_waybel_9 @ sk_A @ 
% 1.49/1.74             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ X0)
% 1.49/1.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74          | ~ (r1_waybel_7 @ sk_A @ sk_B_3 @ X0))),
% 1.49/1.74      inference('sup-', [status(thm)], ['262', '288'])).
% 1.49/1.74  thf('290', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (r1_waybel_7 @ sk_A @ sk_B_3 @ X0)
% 1.49/1.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74          | (r3_waybel_9 @ sk_A @ 
% 1.49/1.74             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ X0)
% 1.49/1.74          | ~ (v4_orders_2 @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ sk_A)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 1.49/1.74      inference('simplify', [status(thm)], ['289'])).
% 1.49/1.74  thf('291', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | (v2_struct_0 @ sk_A)
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74          | (v2_struct_0 @ sk_A)
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | (r3_waybel_9 @ sk_A @ 
% 1.49/1.74             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ X0)
% 1.49/1.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74          | ~ (r1_waybel_7 @ sk_A @ sk_B_3 @ X0))),
% 1.49/1.74      inference('sup-', [status(thm)], ['261', '290'])).
% 1.49/1.74  thf('292', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (r1_waybel_7 @ sk_A @ sk_B_3 @ X0)
% 1.49/1.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.49/1.74          | (r3_waybel_9 @ sk_A @ 
% 1.49/1.74             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ X0)
% 1.49/1.74          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74          | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74          | (v2_struct_0 @ sk_A)
% 1.49/1.74          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 1.49/1.74      inference('simplify', [status(thm)], ['291'])).
% 1.49/1.74  thf('293', plain,
% 1.49/1.74      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | (r3_waybel_9 @ sk_A @ 
% 1.49/1.74            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)
% 1.49/1.74         | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))))
% 1.49/1.74         <= (((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['260', '292'])).
% 1.49/1.74  thf('294', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('295', plain,
% 1.49/1.74      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | (r3_waybel_9 @ sk_A @ 
% 1.49/1.74            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))
% 1.49/1.74         <= (((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('demod', [status(thm)], ['293', '294'])).
% 1.49/1.74  thf('296', plain,
% 1.49/1.74      ((~ (r3_waybel_9 @ sk_A @ 
% 1.49/1.74           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1))
% 1.49/1.74         <= (~
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)))),
% 1.49/1.74      inference('split', [status(esa)], ['0'])).
% 1.49/1.74  thf('297', plain,
% 1.49/1.74      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 1.49/1.74         <= (~
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.74             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['295', '296'])).
% 1.49/1.74  thf('298', plain,
% 1.49/1.74      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74        | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74        | (v2_struct_0 @ sk_A)
% 1.49/1.74        | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['139', '155'])).
% 1.49/1.74  thf('299', plain,
% 1.49/1.74      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 1.49/1.74         <= (~
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.74             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['297', '298'])).
% 1.49/1.74  thf('300', plain,
% 1.49/1.74      (((~ (l1_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 1.49/1.74         <= (~
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.74             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('simplify', [status(thm)], ['299'])).
% 1.49/1.74  thf('301', plain,
% 1.49/1.74      (((~ (l1_pre_topc @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)))
% 1.49/1.74         <= (~
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.74             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['259', '300'])).
% 1.49/1.74  thf('302', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('303', plain,
% 1.49/1.74      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.49/1.74         | (v2_struct_0 @ sk_A)
% 1.49/1.74         | (v1_xboole_0 @ sk_B_3)))
% 1.49/1.74         <= (~
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.74             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('demod', [status(thm)], ['301', '302'])).
% 1.49/1.74  thf('304', plain, (~ (v2_struct_0 @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('305', plain,
% 1.49/1.74      ((((v1_xboole_0 @ sk_B_3) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 1.49/1.74         <= (~
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.74             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('clc', [status(thm)], ['303', '304'])).
% 1.49/1.74  thf('306', plain, (~ (v1_xboole_0 @ sk_B_3)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('307', plain,
% 1.49/1.74      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 1.49/1.74         <= (~
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.74             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('clc', [status(thm)], ['305', '306'])).
% 1.49/1.74  thf('308', plain,
% 1.49/1.74      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 1.49/1.74         <= (~
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.74             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('sup+', [status(thm)], ['258', '307'])).
% 1.49/1.74  thf('309', plain,
% 1.49/1.74      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.49/1.74         <= (~
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.74             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['257', '308'])).
% 1.49/1.74  thf('310', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.74  thf('311', plain,
% 1.49/1.74      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 1.49/1.74         <= (~
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.74             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('demod', [status(thm)], ['309', '310'])).
% 1.49/1.74  thf('312', plain,
% 1.49/1.74      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 1.49/1.74         <= (~
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.74             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('demod', [status(thm)], ['309', '310'])).
% 1.49/1.74  thf('313', plain,
% 1.49/1.74      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_C_1))),
% 1.49/1.74      inference('sup-', [status(thm)], ['174', '175'])).
% 1.49/1.74  thf('314', plain,
% 1.49/1.74      (((v1_xboole_0 @ sk_C_1))
% 1.49/1.74         <= (~
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.74             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['312', '313'])).
% 1.49/1.74  thf('315', plain,
% 1.49/1.74      (![X3 : $i, X4 : $i]:
% 1.49/1.74         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 1.49/1.74      inference('cnf', [status(esa)], [t8_boole])).
% 1.49/1.74  thf('316', plain,
% 1.49/1.74      ((![X0 : $i]: (((sk_C_1) = (X0)) | ~ (v1_xboole_0 @ X0)))
% 1.49/1.74         <= (~
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.74             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['314', '315'])).
% 1.49/1.74  thf('317', plain,
% 1.49/1.74      ((((sk_C_1) = (u1_struct_0 @ sk_A)))
% 1.49/1.74         <= (~
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.74             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['311', '316'])).
% 1.49/1.74  thf('318', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         (~ (l1_struct_0 @ X0)
% 1.49/1.74          | (v7_struct_0 @ X0)
% 1.49/1.74          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.49/1.74          | (v1_xboole_0 @ (sk_C @ X0)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['181', '182'])).
% 1.49/1.74  thf('319', plain,
% 1.49/1.74      (((~ (v1_xboole_0 @ sk_C_1)
% 1.49/1.74         | (v1_xboole_0 @ (sk_C @ sk_A))
% 1.49/1.74         | (v7_struct_0 @ sk_A)
% 1.49/1.74         | ~ (l1_struct_0 @ sk_A)))
% 1.49/1.74         <= (~
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.74             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['317', '318'])).
% 1.49/1.74  thf('320', plain,
% 1.49/1.74      (((v1_xboole_0 @ sk_C_1))
% 1.49/1.74         <= (~
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.74             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['312', '313'])).
% 1.49/1.74  thf('321', plain,
% 1.49/1.74      ((((v1_xboole_0 @ (sk_C @ sk_A))
% 1.49/1.74         | (v7_struct_0 @ sk_A)
% 1.49/1.74         | ~ (l1_struct_0 @ sk_A)))
% 1.49/1.74         <= (~
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.74             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('demod', [status(thm)], ['319', '320'])).
% 1.49/1.74  thf('322', plain,
% 1.49/1.74      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.74  thf('323', plain,
% 1.49/1.74      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 1.49/1.74         <= (~
% 1.49/1.74             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.74             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.74      inference('demod', [status(thm)], ['309', '310'])).
% 1.49/1.74  thf('324', plain,
% 1.49/1.74      (![X0 : $i]:
% 1.49/1.74         ((v2_struct_0 @ X0)
% 1.49/1.74          | ~ (v2_pre_topc @ X0)
% 1.49/1.74          | ~ (l1_pre_topc @ X0)
% 1.49/1.74          | ~ (l1_struct_0 @ X0)
% 1.49/1.74          | ~ (v7_struct_0 @ X0)
% 1.49/1.74          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.49/1.74      inference('sup-', [status(thm)], ['212', '213'])).
% 1.49/1.74  thf('325', plain,
% 1.49/1.74      (((~ (v7_struct_0 @ sk_A)
% 1.49/1.74         | ~ (l1_struct_0 @ sk_A)
% 1.49/1.74         | ~ (l1_pre_topc @ sk_A)
% 1.49/1.74         | ~ (v2_pre_topc @ sk_A)
% 1.49/1.74         | (v2_struct_0 @ sk_A)))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['323', '324'])).
% 1.49/1.75  thf('326', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf('327', plain, ((v2_pre_topc @ sk_A)),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf('328', plain,
% 1.49/1.75      (((~ (v7_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A)))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('demod', [status(thm)], ['325', '326', '327'])).
% 1.49/1.75  thf('329', plain, (~ (v2_struct_0 @ sk_A)),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf('330', plain,
% 1.49/1.75      (((~ (l1_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('clc', [status(thm)], ['328', '329'])).
% 1.49/1.75  thf('331', plain,
% 1.49/1.75      (((~ (l1_pre_topc @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['322', '330'])).
% 1.49/1.75  thf('332', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf('333', plain,
% 1.49/1.75      ((~ (v7_struct_0 @ sk_A))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('demod', [status(thm)], ['331', '332'])).
% 1.49/1.75  thf('334', plain,
% 1.49/1.75      (((~ (l1_struct_0 @ sk_A) | (v1_xboole_0 @ (sk_C @ sk_A))))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('clc', [status(thm)], ['321', '333'])).
% 1.49/1.75  thf('335', plain,
% 1.49/1.75      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (sk_C @ sk_A))))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['256', '334'])).
% 1.49/1.75  thf('336', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf('337', plain,
% 1.49/1.75      (((v1_xboole_0 @ (sk_C @ sk_A)))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('demod', [status(thm)], ['335', '336'])).
% 1.49/1.75  thf('338', plain,
% 1.49/1.75      ((![X0 : $i]: (((sk_C_1) = (X0)) | ~ (v1_xboole_0 @ X0)))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['314', '315'])).
% 1.49/1.75  thf('339', plain,
% 1.49/1.75      ((((sk_C_1) = (sk_C @ sk_A)))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['337', '338'])).
% 1.49/1.75  thf('340', plain,
% 1.49/1.75      (![X26 : $i]:
% 1.49/1.75         (((sk_B_2 @ X26) != (sk_C @ X26))
% 1.49/1.75          | (v7_struct_0 @ X26)
% 1.49/1.75          | ~ (l1_struct_0 @ X26))),
% 1.49/1.75      inference('cnf', [status(esa)], [d10_struct_0])).
% 1.49/1.75  thf('341', plain,
% 1.49/1.75      (((((sk_B_2 @ sk_A) != (sk_C_1))
% 1.49/1.75         | ~ (l1_struct_0 @ sk_A)
% 1.49/1.75         | (v7_struct_0 @ sk_A)))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['339', '340'])).
% 1.49/1.75  thf('342', plain,
% 1.49/1.75      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 1.49/1.75      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.49/1.75  thf('343', plain,
% 1.49/1.75      ((((sk_C_1) = (u1_struct_0 @ sk_A)))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['311', '316'])).
% 1.49/1.75  thf('344', plain,
% 1.49/1.75      (![X0 : $i]:
% 1.49/1.75         (~ (l1_struct_0 @ X0)
% 1.49/1.75          | (v7_struct_0 @ X0)
% 1.49/1.75          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.49/1.75          | (v1_xboole_0 @ (sk_B_2 @ X0)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['234', '235'])).
% 1.49/1.75  thf('345', plain,
% 1.49/1.75      (((~ (v1_xboole_0 @ sk_C_1)
% 1.49/1.75         | (v1_xboole_0 @ (sk_B_2 @ sk_A))
% 1.49/1.75         | (v7_struct_0 @ sk_A)
% 1.49/1.75         | ~ (l1_struct_0 @ sk_A)))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['343', '344'])).
% 1.49/1.75  thf('346', plain,
% 1.49/1.75      (((v1_xboole_0 @ sk_C_1))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['312', '313'])).
% 1.49/1.75  thf('347', plain,
% 1.49/1.75      ((((v1_xboole_0 @ (sk_B_2 @ sk_A))
% 1.49/1.75         | (v7_struct_0 @ sk_A)
% 1.49/1.75         | ~ (l1_struct_0 @ sk_A)))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('demod', [status(thm)], ['345', '346'])).
% 1.49/1.75  thf('348', plain,
% 1.49/1.75      ((~ (v7_struct_0 @ sk_A))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('demod', [status(thm)], ['331', '332'])).
% 1.49/1.75  thf('349', plain,
% 1.49/1.75      (((~ (l1_struct_0 @ sk_A) | (v1_xboole_0 @ (sk_B_2 @ sk_A))))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('clc', [status(thm)], ['347', '348'])).
% 1.49/1.75  thf('350', plain,
% 1.49/1.75      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (sk_B_2 @ sk_A))))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['342', '349'])).
% 1.49/1.75  thf('351', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf('352', plain,
% 1.49/1.75      (((v1_xboole_0 @ (sk_B_2 @ sk_A)))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('demod', [status(thm)], ['350', '351'])).
% 1.49/1.75  thf('353', plain,
% 1.49/1.75      ((![X0 : $i]: (((sk_C_1) = (X0)) | ~ (v1_xboole_0 @ X0)))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['314', '315'])).
% 1.49/1.75  thf('354', plain,
% 1.49/1.75      ((((sk_C_1) = (sk_B_2 @ sk_A)))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['352', '353'])).
% 1.49/1.75  thf('355', plain,
% 1.49/1.75      (((((sk_C_1) != (sk_C_1)) | ~ (l1_struct_0 @ sk_A) | (v7_struct_0 @ sk_A)))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('demod', [status(thm)], ['341', '354'])).
% 1.49/1.75  thf('356', plain,
% 1.49/1.75      ((((v7_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('simplify', [status(thm)], ['355'])).
% 1.49/1.75  thf('357', plain,
% 1.49/1.75      ((~ (v7_struct_0 @ sk_A))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('demod', [status(thm)], ['331', '332'])).
% 1.49/1.75  thf('358', plain,
% 1.49/1.75      ((~ (l1_struct_0 @ sk_A))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('clc', [status(thm)], ['356', '357'])).
% 1.49/1.75  thf('359', plain,
% 1.49/1.75      ((~ (l1_pre_topc @ sk_A))
% 1.49/1.75         <= (~
% 1.49/1.75             ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1)) & 
% 1.49/1.75             ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 1.49/1.75      inference('sup-', [status(thm)], ['255', '358'])).
% 1.49/1.75  thf('360', plain, ((l1_pre_topc @ sk_A)),
% 1.49/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.75  thf('361', plain,
% 1.49/1.75      (~ ((r1_waybel_7 @ sk_A @ sk_B_3 @ sk_C_1)) | 
% 1.49/1.75       ((r3_waybel_9 @ sk_A @ 
% 1.49/1.75         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3) @ sk_C_1))),
% 1.49/1.75      inference('demod', [status(thm)], ['359', '360'])).
% 1.49/1.75  thf('362', plain, ($false),
% 1.49/1.75      inference('sat_resolution*', [status(thm)], ['1', '253', '254', '361'])).
% 1.49/1.75  
% 1.49/1.75  % SZS output end Refutation
% 1.49/1.75  
% 1.49/1.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
