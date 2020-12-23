%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cmuE9lsbcn

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:50 EST 2020

% Result     : Theorem 1.89s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  283 (2267 expanded)
%              Number of leaves         :   48 ( 716 expanded)
%              Depth                    :   42
%              Number of atoms          : 3819 (45589 expanded)
%              Number of equality atoms :   69 ( 686 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

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
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('7',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v1_xboole_0 @ X26 )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( v1_subset_1 @ X28 @ ( u1_struct_0 @ ( k3_yellow_1 @ X26 ) ) )
      | ~ ( v2_waybel_0 @ X28 @ ( k3_yellow_1 @ X26 ) )
      | ~ ( v13_waybel_0 @ X28 @ ( k3_yellow_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X26 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X27 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('10',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('11',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('12',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('13',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('14',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v1_xboole_0 @ X26 )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( v1_subset_1 @ X28 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) )
      | ~ ( v2_waybel_0 @ X28 @ ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) )
      | ~ ( v13_waybel_0 @ X28 @ ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X27 @ X26 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11','12','13'])).

thf('15',plain,(
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
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('18',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('21',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('24',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
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
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','25'])).

thf('27',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('32',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('33',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v1_xboole_0 @ X23 )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v2_waybel_0 @ X25 @ ( k3_yellow_1 @ X23 ) )
      | ~ ( v13_waybel_0 @ X25 @ ( k3_yellow_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X23 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X24 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('35',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('36',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('37',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('38',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v1_xboole_0 @ X23 )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v2_waybel_0 @ X25 @ ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) )
      | ~ ( v13_waybel_0 @ X25 @ ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X24 @ X23 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('41',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
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
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','42'])).

thf('44',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['31','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('49',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('50',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_xboole_0 @ X20 )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( v2_waybel_0 @ X22 @ ( k3_yellow_1 @ X20 ) )
      | ~ ( v13_waybel_0 @ X22 @ ( k3_yellow_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X20 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X21 @ X20 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('52',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('53',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('54',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('55',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_xboole_0 @ X20 )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( v2_waybel_0 @ X22 @ ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) )
      | ~ ( v13_waybel_0 @ X22 @ ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X21 @ X20 @ X22 ) @ X21 ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('58',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
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
    | ( v1_xboole_0 @ sk_B_1 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','59'])).

thf('61',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['48','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v7_waybel_0 @ X29 )
      | ~ ( l1_waybel_0 @ X29 @ X30 )
      | ~ ( r3_waybel_9 @ X30 @ X29 @ X31 )
      | ( r1_waybel_7 @ X30 @ ( k2_yellow19 @ X30 @ X29 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
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
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf('74',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['64','73'])).

thf('75',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('76',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
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

thf('77',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( v1_subset_1 @ X32 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X33 ) ) ) )
      | ~ ( v2_waybel_0 @ X32 @ ( k3_yellow_1 @ ( k2_struct_0 @ X33 ) ) )
      | ~ ( v13_waybel_0 @ X32 @ ( k3_yellow_1 @ ( k2_struct_0 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X33 ) ) ) ) )
      | ( X32
        = ( k2_yellow19 @ X33 @ ( k3_yellow19 @ X33 @ ( k2_struct_0 @ X33 ) @ X32 ) ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('78',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('79',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('80',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('81',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('82',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( v1_subset_1 @ X32 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X33 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X32 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X33 ) ) ) )
      | ~ ( v13_waybel_0 @ X32 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X33 ) ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X33 ) ) ) ) ) )
      | ( X32
        = ( k2_yellow19 @ X33 @ ( k3_yellow19 @ X33 @ ( k2_struct_0 @ X33 ) @ X32 ) ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['76','82'])).

thf('84',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('85',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('86',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( sk_B_1
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['74','94'])).

thf('96',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['47','96'])).

thf('98',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['30','98'])).

thf('100',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('102',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('103',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_xboole_0 @ X20 )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( v2_waybel_0 @ X22 @ ( k3_yellow_1 @ X20 ) )
      | ~ ( v13_waybel_0 @ X22 @ ( k3_yellow_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X20 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X21 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('104',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('105',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('106',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('107',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_xboole_0 @ X20 )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( v2_waybel_0 @ X22 @ ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) )
      | ~ ( v13_waybel_0 @ X22 @ ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X21 @ X20 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['102','107'])).

thf('109',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('110',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
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
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['101','111'])).

thf('113',plain,
    ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['100','113'])).

thf('115',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['3','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
   <= ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('120',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('126',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('127',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('128',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ~ ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ! [X0: $i] :
        ( ( k2_struct_0 @ sk_A )
        = ( k4_xboole_0 @ X0 @ X0 ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['126','132'])).

thf('134',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('135',plain,
    ( ! [X0: $i] :
        ( ( k2_struct_0 @ sk_A )
        = ( k4_xboole_0 @ X0 @ X0 ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['126','132'])).

thf('136',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('137',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['134','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['133','140'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('142',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k7_subset_1 @ X12 @ X11 @ X13 )
        = ( k4_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('143',plain,
    ( ! [X0: $i] :
        ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 )
        = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ X0 ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('145',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ! [X0: $i] :
        ( ( k2_struct_0 @ sk_A )
        = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ X0 ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['144','148'])).

thf('150',plain,
    ( ! [X0: $i] :
        ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 )
        = ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['143','149'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('151',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X10 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('152',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('153',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf(t22_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
            = B ) ) ) )).

thf('154',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k2_struct_0 @ X18 ) @ ( k7_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k2_struct_0 @ X18 ) @ X17 ) )
        = X17 )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t22_pre_topc])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['150','155'])).

thf('157',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_struct_0 @ sk_A )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['125','156'])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['124','159'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('161',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('162',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','164'])).

thf('166',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['65'])).

thf('169',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('170',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('171',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
   <= ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['65'])).

thf('172',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('173',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('174',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('175',plain,
    ( sk_B_1
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('176',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v7_waybel_0 @ X29 )
      | ~ ( l1_waybel_0 @ X29 @ X30 )
      | ~ ( r1_waybel_7 @ X30 @ ( k2_yellow19 @ X30 @ X29 ) @ X31 )
      | ( r3_waybel_9 @ X30 @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('177',plain,(
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
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('181',plain,(
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
    inference('sup-',[status(thm)],['174','180'])).

thf('182',plain,(
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
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
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
    inference('sup-',[status(thm)],['173','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
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
    inference('sup-',[status(thm)],['172','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['171','186'])).

thf('188',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('191',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['112'])).

thf('193',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['170','194'])).

thf('196',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['197','198'])).

thf('200',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('203',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['199','200'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('205',plain,
    ( ! [X0: $i] :
        ( ( k2_struct_0 @ sk_A )
        = ( k4_xboole_0 @ X0 @ X0 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('207',plain,
    ( ! [X0: $i] :
        ( ( k2_struct_0 @ sk_A )
        = ( k4_xboole_0 @ X0 @ X0 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('208',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('209',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['207','208'])).

thf('210',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['206','209'])).

thf('211',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['205','212'])).

thf('214',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k7_subset_1 @ X12 @ X11 @ X13 )
        = ( k4_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('215',plain,
    ( ! [X0: $i] :
        ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 )
        = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ X0 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['199','200'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('218',plain,
    ( ! [X0: $i] :
        ( ( k2_struct_0 @ sk_A )
        = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ X0 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,
    ( ! [X0: $i] :
        ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ X0 )
        = ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['215','218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('221',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['219','220'])).

thf('222',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_struct_0 @ sk_A )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['202','221'])).

thf('223',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['201','224'])).

thf('226',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('227',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['227','228'])).

thf('230',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['169','229'])).

thf('231',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','167','168','232'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cmuE9lsbcn
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:37:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.89/2.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.89/2.12  % Solved by: fo/fo7.sh
% 1.89/2.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.89/2.12  % done 2665 iterations in 1.659s
% 1.89/2.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.89/2.12  % SZS output start Refutation
% 1.89/2.12  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 1.89/2.12  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 1.89/2.12  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.89/2.12  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 1.89/2.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.89/2.12  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.89/2.12  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.89/2.12  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.89/2.12  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.89/2.12  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 1.89/2.12  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.89/2.12  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 1.89/2.12  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 1.89/2.12  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.89/2.12  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.89/2.12  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.89/2.12  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.89/2.12  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.89/2.12  thf(sk_A_type, type, sk_A: $i).
% 1.89/2.12  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 1.89/2.12  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.89/2.12  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 1.89/2.12  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 1.89/2.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.89/2.12  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 1.89/2.12  thf(sk_C_type, type, sk_C: $i).
% 1.89/2.12  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 1.89/2.12  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 1.89/2.12  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 1.89/2.12  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.89/2.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.89/2.12  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 1.89/2.12  thf(t17_yellow19, conjecture,
% 1.89/2.12    (![A:$i]:
% 1.89/2.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.89/2.12       ( ![B:$i]:
% 1.89/2.12         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.89/2.12             ( v1_subset_1 @
% 1.89/2.12               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 1.89/2.12             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.89/2.12             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.89/2.12             ( m1_subset_1 @
% 1.89/2.12               B @ 
% 1.89/2.12               ( k1_zfmisc_1 @
% 1.89/2.12                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 1.89/2.12           ( ![C:$i]:
% 1.89/2.12             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.89/2.12               ( ( r3_waybel_9 @
% 1.89/2.12                   A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 1.89/2.12                 ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 1.89/2.12  thf(zf_stmt_0, negated_conjecture,
% 1.89/2.12    (~( ![A:$i]:
% 1.89/2.12        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.89/2.12            ( l1_pre_topc @ A ) ) =>
% 1.89/2.12          ( ![B:$i]:
% 1.89/2.12            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.89/2.12                ( v1_subset_1 @
% 1.89/2.12                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 1.89/2.12                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.89/2.12                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.89/2.12                ( m1_subset_1 @
% 1.89/2.12                  B @ 
% 1.89/2.12                  ( k1_zfmisc_1 @
% 1.89/2.12                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 1.89/2.12              ( ![C:$i]:
% 1.89/2.12                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.89/2.12                  ( ( r3_waybel_9 @
% 1.89/2.12                      A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 1.89/2.12                    ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 1.89/2.12    inference('cnf.neg', [status(esa)], [t17_yellow19])).
% 1.89/2.12  thf('0', plain,
% 1.89/2.12      ((~ (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 1.89/2.12        | ~ (r3_waybel_9 @ sk_A @ 
% 1.89/2.12             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('1', plain,
% 1.89/2.12      (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) | 
% 1.89/2.12       ~
% 1.89/2.12       ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))),
% 1.89/2.12      inference('split', [status(esa)], ['0'])).
% 1.89/2.12  thf(dt_l1_pre_topc, axiom,
% 1.89/2.12    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.89/2.12  thf('2', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.89/2.12  thf('3', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.89/2.12  thf('4', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.89/2.12  thf(dt_k2_struct_0, axiom,
% 1.89/2.12    (![A:$i]:
% 1.89/2.12     ( ( l1_struct_0 @ A ) =>
% 1.89/2.12       ( m1_subset_1 @
% 1.89/2.12         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.89/2.12  thf('5', plain,
% 1.89/2.12      (![X14 : $i]:
% 1.89/2.12         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 1.89/2.12           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.89/2.12          | ~ (l1_struct_0 @ X14))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.89/2.12  thf('6', plain,
% 1.89/2.12      ((m1_subset_1 @ sk_B_1 @ 
% 1.89/2.12        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf(d2_yellow_1, axiom,
% 1.89/2.12    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 1.89/2.12  thf('7', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('8', plain,
% 1.89/2.12      ((m1_subset_1 @ sk_B_1 @ 
% 1.89/2.12        (k1_zfmisc_1 @ 
% 1.89/2.12         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.89/2.12      inference('demod', [status(thm)], ['6', '7'])).
% 1.89/2.12  thf(fc5_yellow19, axiom,
% 1.89/2.12    (![A:$i,B:$i,C:$i]:
% 1.89/2.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 1.89/2.12         ( ~( v1_xboole_0 @ B ) ) & 
% 1.89/2.12         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.89/2.12         ( ~( v1_xboole_0 @ C ) ) & 
% 1.89/2.12         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 1.89/2.12         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 1.89/2.12         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 1.89/2.12         ( m1_subset_1 @
% 1.89/2.12           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 1.89/2.12       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 1.89/2.12         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 1.89/2.12         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 1.89/2.12  thf('9', plain,
% 1.89/2.12      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.89/2.12         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.89/2.12          | (v1_xboole_0 @ X26)
% 1.89/2.12          | ~ (l1_struct_0 @ X27)
% 1.89/2.12          | (v2_struct_0 @ X27)
% 1.89/2.12          | (v1_xboole_0 @ X28)
% 1.89/2.12          | ~ (v1_subset_1 @ X28 @ (u1_struct_0 @ (k3_yellow_1 @ X26)))
% 1.89/2.12          | ~ (v2_waybel_0 @ X28 @ (k3_yellow_1 @ X26))
% 1.89/2.12          | ~ (v13_waybel_0 @ X28 @ (k3_yellow_1 @ X26))
% 1.89/2.12          | ~ (m1_subset_1 @ X28 @ 
% 1.89/2.12               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X26))))
% 1.89/2.12          | (v7_waybel_0 @ (k3_yellow19 @ X27 @ X26 @ X28)))),
% 1.89/2.12      inference('cnf', [status(esa)], [fc5_yellow19])).
% 1.89/2.12  thf('10', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('11', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('12', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('13', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('14', plain,
% 1.89/2.12      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.89/2.12         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.89/2.12          | (v1_xboole_0 @ X26)
% 1.89/2.12          | ~ (l1_struct_0 @ X27)
% 1.89/2.12          | (v2_struct_0 @ X27)
% 1.89/2.12          | (v1_xboole_0 @ X28)
% 1.89/2.12          | ~ (v1_subset_1 @ X28 @ 
% 1.89/2.12               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X26))))
% 1.89/2.12          | ~ (v2_waybel_0 @ X28 @ (k3_lattice3 @ (k1_lattice3 @ X26)))
% 1.89/2.12          | ~ (v13_waybel_0 @ X28 @ (k3_lattice3 @ (k1_lattice3 @ X26)))
% 1.89/2.12          | ~ (m1_subset_1 @ X28 @ 
% 1.89/2.12               (k1_zfmisc_1 @ 
% 1.89/2.12                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X26)))))
% 1.89/2.12          | (v7_waybel_0 @ (k3_yellow19 @ X27 @ X26 @ X28)))),
% 1.89/2.12      inference('demod', [status(thm)], ['9', '10', '11', '12', '13'])).
% 1.89/2.12  thf('15', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 1.89/2.12               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.89/2.12          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 1.89/2.12               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.89/2.12          | ~ (v1_subset_1 @ sk_B_1 @ 
% 1.89/2.12               (u1_struct_0 @ 
% 1.89/2.12                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 1.89/2.12          | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12          | (v2_struct_0 @ X0)
% 1.89/2.12          | ~ (l1_struct_0 @ X0)
% 1.89/2.12          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.89/2.12               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.89/2.12      inference('sup-', [status(thm)], ['8', '14'])).
% 1.89/2.12  thf('16', plain,
% 1.89/2.12      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('17', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('18', plain,
% 1.89/2.12      ((v13_waybel_0 @ sk_B_1 @ 
% 1.89/2.12        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.89/2.12      inference('demod', [status(thm)], ['16', '17'])).
% 1.89/2.12  thf('19', plain,
% 1.89/2.12      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('20', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('21', plain,
% 1.89/2.12      ((v2_waybel_0 @ sk_B_1 @ 
% 1.89/2.12        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.89/2.12      inference('demod', [status(thm)], ['19', '20'])).
% 1.89/2.12  thf('22', plain,
% 1.89/2.12      ((v1_subset_1 @ sk_B_1 @ 
% 1.89/2.12        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('23', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('24', plain,
% 1.89/2.12      ((v1_subset_1 @ sk_B_1 @ 
% 1.89/2.12        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 1.89/2.12      inference('demod', [status(thm)], ['22', '23'])).
% 1.89/2.12  thf('25', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12          | (v2_struct_0 @ X0)
% 1.89/2.12          | ~ (l1_struct_0 @ X0)
% 1.89/2.12          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.89/2.12               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.89/2.12      inference('demod', [status(thm)], ['15', '18', '21', '24'])).
% 1.89/2.12  thf('26', plain,
% 1.89/2.12      ((~ (l1_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12        | ~ (l1_struct_0 @ sk_A)
% 1.89/2.12        | (v2_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['5', '25'])).
% 1.89/2.12  thf('27', plain,
% 1.89/2.12      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | (v2_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12        | ~ (l1_struct_0 @ sk_A))),
% 1.89/2.12      inference('simplify', [status(thm)], ['26'])).
% 1.89/2.12  thf('28', plain,
% 1.89/2.12      ((~ (l1_pre_topc @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12        | (v2_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['4', '27'])).
% 1.89/2.12  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('30', plain,
% 1.89/2.12      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12        | (v2_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 1.89/2.12      inference('demod', [status(thm)], ['28', '29'])).
% 1.89/2.12  thf('31', plain,
% 1.89/2.12      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.89/2.12  thf('32', plain,
% 1.89/2.12      (![X14 : $i]:
% 1.89/2.12         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 1.89/2.12           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.89/2.12          | ~ (l1_struct_0 @ X14))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.89/2.12  thf('33', plain,
% 1.89/2.12      ((m1_subset_1 @ sk_B_1 @ 
% 1.89/2.12        (k1_zfmisc_1 @ 
% 1.89/2.12         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.89/2.12      inference('demod', [status(thm)], ['6', '7'])).
% 1.89/2.12  thf(fc4_yellow19, axiom,
% 1.89/2.12    (![A:$i,B:$i,C:$i]:
% 1.89/2.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 1.89/2.12         ( ~( v1_xboole_0 @ B ) ) & 
% 1.89/2.12         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.89/2.12         ( ~( v1_xboole_0 @ C ) ) & 
% 1.89/2.12         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 1.89/2.12         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 1.89/2.12         ( m1_subset_1 @
% 1.89/2.12           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 1.89/2.12       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 1.89/2.12         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 1.89/2.12         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 1.89/2.12         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 1.89/2.12  thf('34', plain,
% 1.89/2.12      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.89/2.12         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.89/2.12          | (v1_xboole_0 @ X23)
% 1.89/2.12          | ~ (l1_struct_0 @ X24)
% 1.89/2.12          | (v2_struct_0 @ X24)
% 1.89/2.12          | (v1_xboole_0 @ X25)
% 1.89/2.12          | ~ (v2_waybel_0 @ X25 @ (k3_yellow_1 @ X23))
% 1.89/2.12          | ~ (v13_waybel_0 @ X25 @ (k3_yellow_1 @ X23))
% 1.89/2.12          | ~ (m1_subset_1 @ X25 @ 
% 1.89/2.12               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X23))))
% 1.89/2.12          | (v4_orders_2 @ (k3_yellow19 @ X24 @ X23 @ X25)))),
% 1.89/2.12      inference('cnf', [status(esa)], [fc4_yellow19])).
% 1.89/2.12  thf('35', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('36', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('37', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('38', plain,
% 1.89/2.12      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.89/2.12         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.89/2.12          | (v1_xboole_0 @ X23)
% 1.89/2.12          | ~ (l1_struct_0 @ X24)
% 1.89/2.12          | (v2_struct_0 @ X24)
% 1.89/2.12          | (v1_xboole_0 @ X25)
% 1.89/2.12          | ~ (v2_waybel_0 @ X25 @ (k3_lattice3 @ (k1_lattice3 @ X23)))
% 1.89/2.12          | ~ (v13_waybel_0 @ X25 @ (k3_lattice3 @ (k1_lattice3 @ X23)))
% 1.89/2.12          | ~ (m1_subset_1 @ X25 @ 
% 1.89/2.12               (k1_zfmisc_1 @ 
% 1.89/2.12                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X23)))))
% 1.89/2.12          | (v4_orders_2 @ (k3_yellow19 @ X24 @ X23 @ X25)))),
% 1.89/2.12      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 1.89/2.12  thf('39', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 1.89/2.12               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.89/2.12          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 1.89/2.12               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.89/2.12          | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12          | (v2_struct_0 @ X0)
% 1.89/2.12          | ~ (l1_struct_0 @ X0)
% 1.89/2.12          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.89/2.12               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.89/2.12      inference('sup-', [status(thm)], ['33', '38'])).
% 1.89/2.12  thf('40', plain,
% 1.89/2.12      ((v13_waybel_0 @ sk_B_1 @ 
% 1.89/2.12        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.89/2.12      inference('demod', [status(thm)], ['16', '17'])).
% 1.89/2.12  thf('41', plain,
% 1.89/2.12      ((v2_waybel_0 @ sk_B_1 @ 
% 1.89/2.12        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.89/2.12      inference('demod', [status(thm)], ['19', '20'])).
% 1.89/2.12  thf('42', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12          | (v2_struct_0 @ X0)
% 1.89/2.12          | ~ (l1_struct_0 @ X0)
% 1.89/2.12          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.89/2.12               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.89/2.12      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.89/2.12  thf('43', plain,
% 1.89/2.12      ((~ (l1_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12        | ~ (l1_struct_0 @ sk_A)
% 1.89/2.12        | (v2_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['32', '42'])).
% 1.89/2.12  thf('44', plain,
% 1.89/2.12      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | (v2_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12        | ~ (l1_struct_0 @ sk_A))),
% 1.89/2.12      inference('simplify', [status(thm)], ['43'])).
% 1.89/2.12  thf('45', plain,
% 1.89/2.12      ((~ (l1_pre_topc @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12        | (v2_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['31', '44'])).
% 1.89/2.12  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('47', plain,
% 1.89/2.12      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12        | (v2_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 1.89/2.12      inference('demod', [status(thm)], ['45', '46'])).
% 1.89/2.12  thf('48', plain,
% 1.89/2.12      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.89/2.12  thf('49', plain,
% 1.89/2.12      (![X14 : $i]:
% 1.89/2.12         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 1.89/2.12           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.89/2.12          | ~ (l1_struct_0 @ X14))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.89/2.12  thf('50', plain,
% 1.89/2.12      ((m1_subset_1 @ sk_B_1 @ 
% 1.89/2.12        (k1_zfmisc_1 @ 
% 1.89/2.12         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.89/2.12      inference('demod', [status(thm)], ['6', '7'])).
% 1.89/2.12  thf(dt_k3_yellow19, axiom,
% 1.89/2.12    (![A:$i,B:$i,C:$i]:
% 1.89/2.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 1.89/2.12         ( ~( v1_xboole_0 @ B ) ) & 
% 1.89/2.12         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.89/2.12         ( ~( v1_xboole_0 @ C ) ) & 
% 1.89/2.12         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 1.89/2.12         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 1.89/2.12         ( m1_subset_1 @
% 1.89/2.12           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 1.89/2.12       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 1.89/2.12         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 1.89/2.12         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 1.89/2.12  thf('51', plain,
% 1.89/2.12      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.89/2.12         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.89/2.12          | (v1_xboole_0 @ X20)
% 1.89/2.12          | ~ (l1_struct_0 @ X21)
% 1.89/2.12          | (v2_struct_0 @ X21)
% 1.89/2.12          | (v1_xboole_0 @ X22)
% 1.89/2.12          | ~ (v2_waybel_0 @ X22 @ (k3_yellow_1 @ X20))
% 1.89/2.12          | ~ (v13_waybel_0 @ X22 @ (k3_yellow_1 @ X20))
% 1.89/2.12          | ~ (m1_subset_1 @ X22 @ 
% 1.89/2.12               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X20))))
% 1.89/2.12          | (l1_waybel_0 @ (k3_yellow19 @ X21 @ X20 @ X22) @ X21))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 1.89/2.12  thf('52', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('53', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('54', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('55', plain,
% 1.89/2.12      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.89/2.12         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.89/2.12          | (v1_xboole_0 @ X20)
% 1.89/2.12          | ~ (l1_struct_0 @ X21)
% 1.89/2.12          | (v2_struct_0 @ X21)
% 1.89/2.12          | (v1_xboole_0 @ X22)
% 1.89/2.12          | ~ (v2_waybel_0 @ X22 @ (k3_lattice3 @ (k1_lattice3 @ X20)))
% 1.89/2.12          | ~ (v13_waybel_0 @ X22 @ (k3_lattice3 @ (k1_lattice3 @ X20)))
% 1.89/2.12          | ~ (m1_subset_1 @ X22 @ 
% 1.89/2.12               (k1_zfmisc_1 @ 
% 1.89/2.12                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X20)))))
% 1.89/2.12          | (l1_waybel_0 @ (k3_yellow19 @ X21 @ X20 @ X22) @ X21))),
% 1.89/2.12      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 1.89/2.12  thf('56', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 1.89/2.12           X0)
% 1.89/2.12          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 1.89/2.12               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.89/2.12          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 1.89/2.12               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.89/2.12          | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12          | (v2_struct_0 @ X0)
% 1.89/2.12          | ~ (l1_struct_0 @ X0)
% 1.89/2.12          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.89/2.12               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.89/2.12      inference('sup-', [status(thm)], ['50', '55'])).
% 1.89/2.12  thf('57', plain,
% 1.89/2.12      ((v13_waybel_0 @ sk_B_1 @ 
% 1.89/2.12        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.89/2.12      inference('demod', [status(thm)], ['16', '17'])).
% 1.89/2.12  thf('58', plain,
% 1.89/2.12      ((v2_waybel_0 @ sk_B_1 @ 
% 1.89/2.12        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.89/2.12      inference('demod', [status(thm)], ['19', '20'])).
% 1.89/2.12  thf('59', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 1.89/2.12           X0)
% 1.89/2.12          | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12          | (v2_struct_0 @ X0)
% 1.89/2.12          | ~ (l1_struct_0 @ X0)
% 1.89/2.12          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.89/2.12               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.89/2.12      inference('demod', [status(thm)], ['56', '57', '58'])).
% 1.89/2.12  thf('60', plain,
% 1.89/2.12      ((~ (l1_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12        | ~ (l1_struct_0 @ sk_A)
% 1.89/2.12        | (v2_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | (l1_waybel_0 @ 
% 1.89/2.12           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 1.89/2.12      inference('sup-', [status(thm)], ['49', '59'])).
% 1.89/2.12  thf('61', plain,
% 1.89/2.12      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 1.89/2.12         sk_A)
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | (v2_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12        | ~ (l1_struct_0 @ sk_A))),
% 1.89/2.12      inference('simplify', [status(thm)], ['60'])).
% 1.89/2.12  thf('62', plain,
% 1.89/2.12      ((~ (l1_pre_topc @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12        | (v2_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | (l1_waybel_0 @ 
% 1.89/2.12           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 1.89/2.12      inference('sup-', [status(thm)], ['48', '61'])).
% 1.89/2.12  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('64', plain,
% 1.89/2.12      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12        | (v2_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | (l1_waybel_0 @ 
% 1.89/2.12           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 1.89/2.12      inference('demod', [status(thm)], ['62', '63'])).
% 1.89/2.12  thf('65', plain,
% 1.89/2.12      (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 1.89/2.12        | (r3_waybel_9 @ sk_A @ 
% 1.89/2.12           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('66', plain,
% 1.89/2.12      (((r3_waybel_9 @ sk_A @ 
% 1.89/2.12         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))
% 1.89/2.12         <= (((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('split', [status(esa)], ['65'])).
% 1.89/2.12  thf('67', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf(t12_yellow19, axiom,
% 1.89/2.12    (![A:$i]:
% 1.89/2.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.89/2.12       ( ![B:$i]:
% 1.89/2.12         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 1.89/2.12             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 1.89/2.12           ( ![C:$i]:
% 1.89/2.12             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.89/2.12               ( ( r3_waybel_9 @ A @ B @ C ) <=>
% 1.89/2.12                 ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 1.89/2.12  thf('68', plain,
% 1.89/2.12      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.89/2.12         ((v2_struct_0 @ X29)
% 1.89/2.12          | ~ (v4_orders_2 @ X29)
% 1.89/2.12          | ~ (v7_waybel_0 @ X29)
% 1.89/2.12          | ~ (l1_waybel_0 @ X29 @ X30)
% 1.89/2.12          | ~ (r3_waybel_9 @ X30 @ X29 @ X31)
% 1.89/2.12          | (r1_waybel_7 @ X30 @ (k2_yellow19 @ X30 @ X29) @ X31)
% 1.89/2.12          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 1.89/2.12          | ~ (l1_pre_topc @ X30)
% 1.89/2.12          | ~ (v2_pre_topc @ X30)
% 1.89/2.12          | (v2_struct_0 @ X30))),
% 1.89/2.12      inference('cnf', [status(esa)], [t12_yellow19])).
% 1.89/2.12  thf('69', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         ((v2_struct_0 @ sk_A)
% 1.89/2.12          | ~ (v2_pre_topc @ sk_A)
% 1.89/2.12          | ~ (l1_pre_topc @ sk_A)
% 1.89/2.12          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 1.89/2.12          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 1.89/2.12          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 1.89/2.12          | ~ (v7_waybel_0 @ X0)
% 1.89/2.12          | ~ (v4_orders_2 @ X0)
% 1.89/2.12          | (v2_struct_0 @ X0))),
% 1.89/2.12      inference('sup-', [status(thm)], ['67', '68'])).
% 1.89/2.12  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('72', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         ((v2_struct_0 @ sk_A)
% 1.89/2.12          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 1.89/2.12          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 1.89/2.12          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 1.89/2.12          | ~ (v7_waybel_0 @ X0)
% 1.89/2.12          | ~ (v4_orders_2 @ X0)
% 1.89/2.12          | (v2_struct_0 @ X0))),
% 1.89/2.12      inference('demod', [status(thm)], ['69', '70', '71'])).
% 1.89/2.12  thf('73', plain,
% 1.89/2.12      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12         | ~ (v4_orders_2 @ 
% 1.89/2.12              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12         | ~ (v7_waybel_0 @ 
% 1.89/2.12              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12         | ~ (l1_waybel_0 @ 
% 1.89/2.12              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 1.89/2.12         | (r1_waybel_7 @ sk_A @ 
% 1.89/2.12            (k2_yellow19 @ sk_A @ 
% 1.89/2.12             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 1.89/2.12            sk_C)
% 1.89/2.12         | (v2_struct_0 @ sk_A)))
% 1.89/2.12         <= (((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['66', '72'])).
% 1.89/2.12  thf('74', plain,
% 1.89/2.12      ((((v1_xboole_0 @ sk_B_1)
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (r1_waybel_7 @ sk_A @ 
% 1.89/2.12            (k2_yellow19 @ sk_A @ 
% 1.89/2.12             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 1.89/2.12            sk_C)
% 1.89/2.12         | ~ (v7_waybel_0 @ 
% 1.89/2.12              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12         | ~ (v4_orders_2 @ 
% 1.89/2.12              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 1.89/2.12         <= (((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['64', '73'])).
% 1.89/2.12  thf('75', plain,
% 1.89/2.12      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.89/2.12  thf('76', plain,
% 1.89/2.12      ((m1_subset_1 @ sk_B_1 @ 
% 1.89/2.12        (k1_zfmisc_1 @ 
% 1.89/2.12         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.89/2.12      inference('demod', [status(thm)], ['6', '7'])).
% 1.89/2.12  thf(t15_yellow19, axiom,
% 1.89/2.12    (![A:$i]:
% 1.89/2.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.89/2.12       ( ![B:$i]:
% 1.89/2.12         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.89/2.12             ( v1_subset_1 @
% 1.89/2.12               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 1.89/2.12             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.89/2.12             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.89/2.12             ( m1_subset_1 @
% 1.89/2.12               B @ 
% 1.89/2.12               ( k1_zfmisc_1 @
% 1.89/2.12                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 1.89/2.12           ( ( B ) =
% 1.89/2.12             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 1.89/2.12  thf('77', plain,
% 1.89/2.12      (![X32 : $i, X33 : $i]:
% 1.89/2.12         ((v1_xboole_0 @ X32)
% 1.89/2.12          | ~ (v1_subset_1 @ X32 @ 
% 1.89/2.12               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X33))))
% 1.89/2.12          | ~ (v2_waybel_0 @ X32 @ (k3_yellow_1 @ (k2_struct_0 @ X33)))
% 1.89/2.12          | ~ (v13_waybel_0 @ X32 @ (k3_yellow_1 @ (k2_struct_0 @ X33)))
% 1.89/2.12          | ~ (m1_subset_1 @ X32 @ 
% 1.89/2.12               (k1_zfmisc_1 @ 
% 1.89/2.12                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X33)))))
% 1.89/2.12          | ((X32)
% 1.89/2.12              = (k2_yellow19 @ X33 @ 
% 1.89/2.12                 (k3_yellow19 @ X33 @ (k2_struct_0 @ X33) @ X32)))
% 1.89/2.12          | ~ (l1_struct_0 @ X33)
% 1.89/2.12          | (v2_struct_0 @ X33))),
% 1.89/2.12      inference('cnf', [status(esa)], [t15_yellow19])).
% 1.89/2.12  thf('78', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('79', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('80', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('81', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('82', plain,
% 1.89/2.12      (![X32 : $i, X33 : $i]:
% 1.89/2.12         ((v1_xboole_0 @ X32)
% 1.89/2.12          | ~ (v1_subset_1 @ X32 @ 
% 1.89/2.12               (u1_struct_0 @ 
% 1.89/2.12                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X33)))))
% 1.89/2.12          | ~ (v2_waybel_0 @ X32 @ 
% 1.89/2.12               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X33))))
% 1.89/2.12          | ~ (v13_waybel_0 @ X32 @ 
% 1.89/2.12               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X33))))
% 1.89/2.12          | ~ (m1_subset_1 @ X32 @ 
% 1.89/2.12               (k1_zfmisc_1 @ 
% 1.89/2.12                (u1_struct_0 @ 
% 1.89/2.12                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X33))))))
% 1.89/2.12          | ((X32)
% 1.89/2.12              = (k2_yellow19 @ X33 @ 
% 1.89/2.12                 (k3_yellow19 @ X33 @ (k2_struct_0 @ X33) @ X32)))
% 1.89/2.12          | ~ (l1_struct_0 @ X33)
% 1.89/2.12          | (v2_struct_0 @ X33))),
% 1.89/2.12      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 1.89/2.12  thf('83', plain,
% 1.89/2.12      (((v2_struct_0 @ sk_A)
% 1.89/2.12        | ~ (l1_struct_0 @ sk_A)
% 1.89/2.12        | ((sk_B_1)
% 1.89/2.12            = (k2_yellow19 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 1.89/2.12        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 1.89/2.12             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.89/2.12        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 1.89/2.12             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.89/2.12        | ~ (v1_subset_1 @ sk_B_1 @ 
% 1.89/2.12             (u1_struct_0 @ 
% 1.89/2.12              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1))),
% 1.89/2.12      inference('sup-', [status(thm)], ['76', '82'])).
% 1.89/2.12  thf('84', plain,
% 1.89/2.12      ((v13_waybel_0 @ sk_B_1 @ 
% 1.89/2.12        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.89/2.12      inference('demod', [status(thm)], ['16', '17'])).
% 1.89/2.12  thf('85', plain,
% 1.89/2.12      ((v2_waybel_0 @ sk_B_1 @ 
% 1.89/2.12        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.89/2.12      inference('demod', [status(thm)], ['19', '20'])).
% 1.89/2.12  thf('86', plain,
% 1.89/2.12      ((v1_subset_1 @ sk_B_1 @ 
% 1.89/2.12        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 1.89/2.12      inference('demod', [status(thm)], ['22', '23'])).
% 1.89/2.12  thf('87', plain,
% 1.89/2.12      (((v2_struct_0 @ sk_A)
% 1.89/2.12        | ~ (l1_struct_0 @ sk_A)
% 1.89/2.12        | ((sk_B_1)
% 1.89/2.12            = (k2_yellow19 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1))),
% 1.89/2.12      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 1.89/2.12  thf('88', plain,
% 1.89/2.12      ((~ (l1_pre_topc @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | ((sk_B_1)
% 1.89/2.12            = (k2_yellow19 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 1.89/2.12        | (v2_struct_0 @ sk_A))),
% 1.89/2.12      inference('sup-', [status(thm)], ['75', '87'])).
% 1.89/2.12  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('90', plain,
% 1.89/2.12      (((v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | ((sk_B_1)
% 1.89/2.12            = (k2_yellow19 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 1.89/2.12        | (v2_struct_0 @ sk_A))),
% 1.89/2.12      inference('demod', [status(thm)], ['88', '89'])).
% 1.89/2.12  thf('91', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('92', plain,
% 1.89/2.12      (((v2_struct_0 @ sk_A)
% 1.89/2.12        | ((sk_B_1)
% 1.89/2.12            = (k2_yellow19 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 1.89/2.12      inference('clc', [status(thm)], ['90', '91'])).
% 1.89/2.12  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('94', plain,
% 1.89/2.12      (((sk_B_1)
% 1.89/2.12         = (k2_yellow19 @ sk_A @ 
% 1.89/2.12            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 1.89/2.12      inference('clc', [status(thm)], ['92', '93'])).
% 1.89/2.12  thf('95', plain,
% 1.89/2.12      ((((v1_xboole_0 @ sk_B_1)
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 1.89/2.12         | ~ (v7_waybel_0 @ 
% 1.89/2.12              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12         | ~ (v4_orders_2 @ 
% 1.89/2.12              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 1.89/2.12         <= (((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('demod', [status(thm)], ['74', '94'])).
% 1.89/2.12  thf('96', plain,
% 1.89/2.12      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12         | ~ (v4_orders_2 @ 
% 1.89/2.12              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12         | ~ (v7_waybel_0 @ 
% 1.89/2.12              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ sk_B_1)))
% 1.89/2.12         <= (((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('simplify', [status(thm)], ['95'])).
% 1.89/2.12  thf('97', plain,
% 1.89/2.12      ((((v1_xboole_0 @ sk_B_1)
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 1.89/2.12         | ~ (v7_waybel_0 @ 
% 1.89/2.12              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 1.89/2.12         <= (((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['47', '96'])).
% 1.89/2.12  thf('98', plain,
% 1.89/2.12      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12         | ~ (v7_waybel_0 @ 
% 1.89/2.12              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ sk_B_1)))
% 1.89/2.12         <= (((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('simplify', [status(thm)], ['97'])).
% 1.89/2.12  thf('99', plain,
% 1.89/2.12      ((((v1_xboole_0 @ sk_B_1)
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 1.89/2.12         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 1.89/2.12         <= (((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['30', '98'])).
% 1.89/2.12  thf('100', plain,
% 1.89/2.12      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ sk_B_1)))
% 1.89/2.12         <= (((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('simplify', [status(thm)], ['99'])).
% 1.89/2.12  thf('101', plain,
% 1.89/2.12      (![X14 : $i]:
% 1.89/2.12         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 1.89/2.12           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.89/2.12          | ~ (l1_struct_0 @ X14))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.89/2.12  thf('102', plain,
% 1.89/2.12      ((m1_subset_1 @ sk_B_1 @ 
% 1.89/2.12        (k1_zfmisc_1 @ 
% 1.89/2.12         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.89/2.12      inference('demod', [status(thm)], ['6', '7'])).
% 1.89/2.12  thf('103', plain,
% 1.89/2.12      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.89/2.12         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.89/2.12          | (v1_xboole_0 @ X20)
% 1.89/2.12          | ~ (l1_struct_0 @ X21)
% 1.89/2.12          | (v2_struct_0 @ X21)
% 1.89/2.12          | (v1_xboole_0 @ X22)
% 1.89/2.12          | ~ (v2_waybel_0 @ X22 @ (k3_yellow_1 @ X20))
% 1.89/2.12          | ~ (v13_waybel_0 @ X22 @ (k3_yellow_1 @ X20))
% 1.89/2.12          | ~ (m1_subset_1 @ X22 @ 
% 1.89/2.12               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X20))))
% 1.89/2.12          | ~ (v2_struct_0 @ (k3_yellow19 @ X21 @ X20 @ X22)))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 1.89/2.12  thf('104', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('105', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('106', plain,
% 1.89/2.12      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 1.89/2.12      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.89/2.12  thf('107', plain,
% 1.89/2.12      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.89/2.12         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.89/2.12          | (v1_xboole_0 @ X20)
% 1.89/2.12          | ~ (l1_struct_0 @ X21)
% 1.89/2.12          | (v2_struct_0 @ X21)
% 1.89/2.12          | (v1_xboole_0 @ X22)
% 1.89/2.12          | ~ (v2_waybel_0 @ X22 @ (k3_lattice3 @ (k1_lattice3 @ X20)))
% 1.89/2.12          | ~ (v13_waybel_0 @ X22 @ (k3_lattice3 @ (k1_lattice3 @ X20)))
% 1.89/2.12          | ~ (m1_subset_1 @ X22 @ 
% 1.89/2.12               (k1_zfmisc_1 @ 
% 1.89/2.12                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X20)))))
% 1.89/2.12          | ~ (v2_struct_0 @ (k3_yellow19 @ X21 @ X20 @ X22)))),
% 1.89/2.12      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 1.89/2.12  thf('108', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 1.89/2.12               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.89/2.12          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 1.89/2.12               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.89/2.12          | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12          | (v2_struct_0 @ X0)
% 1.89/2.12          | ~ (l1_struct_0 @ X0)
% 1.89/2.12          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.89/2.12               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.89/2.12      inference('sup-', [status(thm)], ['102', '107'])).
% 1.89/2.12  thf('109', plain,
% 1.89/2.12      ((v13_waybel_0 @ sk_B_1 @ 
% 1.89/2.12        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.89/2.12      inference('demod', [status(thm)], ['16', '17'])).
% 1.89/2.12  thf('110', plain,
% 1.89/2.12      ((v2_waybel_0 @ sk_B_1 @ 
% 1.89/2.12        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.89/2.12      inference('demod', [status(thm)], ['19', '20'])).
% 1.89/2.12  thf('111', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12          | (v2_struct_0 @ X0)
% 1.89/2.12          | ~ (l1_struct_0 @ X0)
% 1.89/2.12          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.89/2.12               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.89/2.12      inference('demod', [status(thm)], ['108', '109', '110'])).
% 1.89/2.12  thf('112', plain,
% 1.89/2.12      ((~ (l1_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12        | ~ (l1_struct_0 @ sk_A)
% 1.89/2.12        | (v2_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['101', '111'])).
% 1.89/2.12  thf('113', plain,
% 1.89/2.12      ((~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | (v2_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12        | ~ (l1_struct_0 @ sk_A))),
% 1.89/2.12      inference('simplify', [status(thm)], ['112'])).
% 1.89/2.12  thf('114', plain,
% 1.89/2.12      ((((v1_xboole_0 @ sk_B_1)
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 1.89/2.12         | ~ (l1_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ sk_B_1)))
% 1.89/2.12         <= (((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['100', '113'])).
% 1.89/2.12  thf('115', plain,
% 1.89/2.12      (((~ (l1_struct_0 @ sk_A)
% 1.89/2.12         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ sk_B_1)))
% 1.89/2.12         <= (((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('simplify', [status(thm)], ['114'])).
% 1.89/2.12  thf('116', plain,
% 1.89/2.12      (((~ (l1_pre_topc @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))
% 1.89/2.12         <= (((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['3', '115'])).
% 1.89/2.12  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('118', plain,
% 1.89/2.12      ((((v1_xboole_0 @ sk_B_1)
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))
% 1.89/2.12         <= (((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('demod', [status(thm)], ['116', '117'])).
% 1.89/2.12  thf('119', plain,
% 1.89/2.12      ((~ (r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('split', [status(esa)], ['0'])).
% 1.89/2.12  thf('120', plain,
% 1.89/2.12      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ sk_B_1)))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['118', '119'])).
% 1.89/2.12  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('122', plain,
% 1.89/2.12      ((((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('clc', [status(thm)], ['120', '121'])).
% 1.89/2.12  thf('123', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('124', plain,
% 1.89/2.12      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('clc', [status(thm)], ['122', '123'])).
% 1.89/2.12  thf('125', plain,
% 1.89/2.12      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.89/2.12  thf('126', plain,
% 1.89/2.12      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('clc', [status(thm)], ['122', '123'])).
% 1.89/2.12  thf(d5_xboole_0, axiom,
% 1.89/2.12    (![A:$i,B:$i,C:$i]:
% 1.89/2.12     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.89/2.12       ( ![D:$i]:
% 1.89/2.12         ( ( r2_hidden @ D @ C ) <=>
% 1.89/2.12           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.89/2.12  thf('127', plain,
% 1.89/2.12      (![X4 : $i, X5 : $i, X8 : $i]:
% 1.89/2.12         (((X8) = (k4_xboole_0 @ X4 @ X5))
% 1.89/2.12          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X4)
% 1.89/2.12          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 1.89/2.12      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.89/2.12  thf('128', plain,
% 1.89/2.12      (![X4 : $i, X5 : $i, X8 : $i]:
% 1.89/2.12         (((X8) = (k4_xboole_0 @ X4 @ X5))
% 1.89/2.12          | ~ (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X5)
% 1.89/2.12          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 1.89/2.12      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.89/2.12  thf('129', plain,
% 1.89/2.12      (![X0 : $i, X1 : $i]:
% 1.89/2.12         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.89/2.12          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.89/2.12          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.89/2.12          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['127', '128'])).
% 1.89/2.12  thf('130', plain,
% 1.89/2.12      (![X0 : $i, X1 : $i]:
% 1.89/2.12         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.89/2.12          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.89/2.12      inference('simplify', [status(thm)], ['129'])).
% 1.89/2.12  thf(d1_xboole_0, axiom,
% 1.89/2.12    (![A:$i]:
% 1.89/2.12     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.89/2.12  thf('131', plain,
% 1.89/2.12      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.89/2.12      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.89/2.12  thf('132', plain,
% 1.89/2.12      (![X0 : $i, X1 : $i]:
% 1.89/2.12         (((X0) = (k4_xboole_0 @ X1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.89/2.12      inference('sup-', [status(thm)], ['130', '131'])).
% 1.89/2.12  thf('133', plain,
% 1.89/2.12      ((![X0 : $i]: ((k2_struct_0 @ sk_A) = (k4_xboole_0 @ X0 @ X0)))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['126', '132'])).
% 1.89/2.12  thf('134', plain,
% 1.89/2.12      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.89/2.12  thf('135', plain,
% 1.89/2.12      ((![X0 : $i]: ((k2_struct_0 @ sk_A) = (k4_xboole_0 @ X0 @ X0)))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['126', '132'])).
% 1.89/2.12  thf('136', plain,
% 1.89/2.12      (![X14 : $i]:
% 1.89/2.12         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 1.89/2.12           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.89/2.12          | ~ (l1_struct_0 @ X14))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.89/2.12  thf('137', plain,
% 1.89/2.12      ((![X0 : $i]:
% 1.89/2.12          ((m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ 
% 1.89/2.12            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.89/2.12           | ~ (l1_struct_0 @ sk_A)))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('sup+', [status(thm)], ['135', '136'])).
% 1.89/2.12  thf('138', plain,
% 1.89/2.12      ((![X0 : $i]:
% 1.89/2.12          (~ (l1_pre_topc @ sk_A)
% 1.89/2.12           | (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ 
% 1.89/2.12              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['134', '137'])).
% 1.89/2.12  thf('139', plain, ((l1_pre_topc @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('140', plain,
% 1.89/2.12      ((![X0 : $i]:
% 1.89/2.12          (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ 
% 1.89/2.12           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('demod', [status(thm)], ['138', '139'])).
% 1.89/2.12  thf('141', plain,
% 1.89/2.12      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.89/2.12         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('sup+', [status(thm)], ['133', '140'])).
% 1.89/2.12  thf(redefinition_k7_subset_1, axiom,
% 1.89/2.12    (![A:$i,B:$i,C:$i]:
% 1.89/2.12     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.89/2.12       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.89/2.12  thf('142', plain,
% 1.89/2.12      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.89/2.12         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 1.89/2.12          | ((k7_subset_1 @ X12 @ X11 @ X13) = (k4_xboole_0 @ X11 @ X13)))),
% 1.89/2.12      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.89/2.12  thf('143', plain,
% 1.89/2.12      ((![X0 : $i]:
% 1.89/2.12          ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0)
% 1.89/2.12            = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ X0)))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['141', '142'])).
% 1.89/2.12  thf('144', plain,
% 1.89/2.12      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('clc', [status(thm)], ['122', '123'])).
% 1.89/2.12  thf('145', plain,
% 1.89/2.12      (![X4 : $i, X5 : $i, X8 : $i]:
% 1.89/2.12         (((X8) = (k4_xboole_0 @ X4 @ X5))
% 1.89/2.12          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X4)
% 1.89/2.12          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 1.89/2.12      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.89/2.12  thf('146', plain,
% 1.89/2.12      (![X0 : $i, X1 : $i]:
% 1.89/2.12         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.89/2.12          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.89/2.12      inference('eq_fact', [status(thm)], ['145'])).
% 1.89/2.12  thf('147', plain,
% 1.89/2.12      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.89/2.12      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.89/2.12  thf('148', plain,
% 1.89/2.12      (![X0 : $i, X1 : $i]:
% 1.89/2.12         (((X0) = (k4_xboole_0 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.89/2.12      inference('sup-', [status(thm)], ['146', '147'])).
% 1.89/2.12  thf('149', plain,
% 1.89/2.12      ((![X0 : $i]:
% 1.89/2.12          ((k2_struct_0 @ sk_A) = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ X0)))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['144', '148'])).
% 1.89/2.12  thf('150', plain,
% 1.89/2.12      ((![X0 : $i]:
% 1.89/2.12          ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0)
% 1.89/2.12            = (k2_struct_0 @ sk_A)))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('demod', [status(thm)], ['143', '149'])).
% 1.89/2.12  thf(dt_k2_subset_1, axiom,
% 1.89/2.12    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.89/2.12  thf('151', plain,
% 1.89/2.12      (![X10 : $i]: (m1_subset_1 @ (k2_subset_1 @ X10) @ (k1_zfmisc_1 @ X10))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.89/2.12  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.89/2.12  thf('152', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 1.89/2.12      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.89/2.12  thf('153', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 1.89/2.12      inference('demod', [status(thm)], ['151', '152'])).
% 1.89/2.12  thf(t22_pre_topc, axiom,
% 1.89/2.12    (![A:$i]:
% 1.89/2.12     ( ( l1_struct_0 @ A ) =>
% 1.89/2.12       ( ![B:$i]:
% 1.89/2.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.89/2.12           ( ( k7_subset_1 @
% 1.89/2.12               ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ 
% 1.89/2.12               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 1.89/2.12             ( B ) ) ) ) ))).
% 1.89/2.12  thf('154', plain,
% 1.89/2.12      (![X17 : $i, X18 : $i]:
% 1.89/2.12         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.89/2.12          | ((k7_subset_1 @ (u1_struct_0 @ X18) @ (k2_struct_0 @ X18) @ 
% 1.89/2.12              (k7_subset_1 @ (u1_struct_0 @ X18) @ (k2_struct_0 @ X18) @ X17))
% 1.89/2.12              = (X17))
% 1.89/2.12          | ~ (l1_struct_0 @ X18))),
% 1.89/2.12      inference('cnf', [status(esa)], [t22_pre_topc])).
% 1.89/2.12  thf('155', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         (~ (l1_struct_0 @ X0)
% 1.89/2.12          | ((k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ 
% 1.89/2.12              (k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ 
% 1.89/2.12               (u1_struct_0 @ X0)))
% 1.89/2.12              = (u1_struct_0 @ X0)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['153', '154'])).
% 1.89/2.12  thf('156', plain,
% 1.89/2.12      (((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('sup+', [status(thm)], ['150', '155'])).
% 1.89/2.12  thf('157', plain,
% 1.89/2.12      (((~ (l1_pre_topc @ sk_A) | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['125', '156'])).
% 1.89/2.12  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('159', plain,
% 1.89/2.12      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('demod', [status(thm)], ['157', '158'])).
% 1.89/2.12  thf('160', plain,
% 1.89/2.12      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('demod', [status(thm)], ['124', '159'])).
% 1.89/2.12  thf(fc2_struct_0, axiom,
% 1.89/2.12    (![A:$i]:
% 1.89/2.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.89/2.12       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.89/2.12  thf('161', plain,
% 1.89/2.12      (![X16 : $i]:
% 1.89/2.12         (~ (v1_xboole_0 @ (u1_struct_0 @ X16))
% 1.89/2.12          | ~ (l1_struct_0 @ X16)
% 1.89/2.12          | (v2_struct_0 @ X16))),
% 1.89/2.12      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.89/2.12  thf('162', plain,
% 1.89/2.12      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['160', '161'])).
% 1.89/2.12  thf('163', plain, (~ (v2_struct_0 @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('164', plain,
% 1.89/2.12      ((~ (l1_struct_0 @ sk_A))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('clc', [status(thm)], ['162', '163'])).
% 1.89/2.12  thf('165', plain,
% 1.89/2.12      ((~ (l1_pre_topc @ sk_A))
% 1.89/2.12         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) & 
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['2', '164'])).
% 1.89/2.12  thf('166', plain, ((l1_pre_topc @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('167', plain,
% 1.89/2.12      (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) | 
% 1.89/2.12       ~
% 1.89/2.12       ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))),
% 1.89/2.12      inference('demod', [status(thm)], ['165', '166'])).
% 1.89/2.12  thf('168', plain,
% 1.89/2.12      (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) | 
% 1.89/2.12       ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))),
% 1.89/2.12      inference('split', [status(esa)], ['65'])).
% 1.89/2.12  thf('169', plain,
% 1.89/2.12      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.89/2.12  thf('170', plain,
% 1.89/2.12      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.89/2.12  thf('171', plain,
% 1.89/2.12      (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C))
% 1.89/2.12         <= (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('split', [status(esa)], ['65'])).
% 1.89/2.12  thf('172', plain,
% 1.89/2.12      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12        | (v2_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 1.89/2.12      inference('demod', [status(thm)], ['45', '46'])).
% 1.89/2.12  thf('173', plain,
% 1.89/2.12      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12        | (v2_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 1.89/2.12      inference('demod', [status(thm)], ['28', '29'])).
% 1.89/2.12  thf('174', plain,
% 1.89/2.12      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12        | (v2_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | (l1_waybel_0 @ 
% 1.89/2.12           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 1.89/2.12      inference('demod', [status(thm)], ['62', '63'])).
% 1.89/2.12  thf('175', plain,
% 1.89/2.12      (((sk_B_1)
% 1.89/2.12         = (k2_yellow19 @ sk_A @ 
% 1.89/2.12            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 1.89/2.12      inference('clc', [status(thm)], ['92', '93'])).
% 1.89/2.12  thf('176', plain,
% 1.89/2.12      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.89/2.12         ((v2_struct_0 @ X29)
% 1.89/2.12          | ~ (v4_orders_2 @ X29)
% 1.89/2.12          | ~ (v7_waybel_0 @ X29)
% 1.89/2.12          | ~ (l1_waybel_0 @ X29 @ X30)
% 1.89/2.12          | ~ (r1_waybel_7 @ X30 @ (k2_yellow19 @ X30 @ X29) @ X31)
% 1.89/2.12          | (r3_waybel_9 @ X30 @ X29 @ X31)
% 1.89/2.12          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 1.89/2.12          | ~ (l1_pre_topc @ X30)
% 1.89/2.12          | ~ (v2_pre_topc @ X30)
% 1.89/2.12          | (v2_struct_0 @ X30))),
% 1.89/2.12      inference('cnf', [status(esa)], [t12_yellow19])).
% 1.89/2.12  thf('177', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         (~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 1.89/2.12          | (v2_struct_0 @ sk_A)
% 1.89/2.12          | ~ (v2_pre_topc @ sk_A)
% 1.89/2.12          | ~ (l1_pre_topc @ sk_A)
% 1.89/2.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.89/2.12          | (r3_waybel_9 @ sk_A @ 
% 1.89/2.12             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 1.89/2.12          | ~ (l1_waybel_0 @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 1.89/2.12          | ~ (v7_waybel_0 @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | ~ (v4_orders_2 @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['175', '176'])).
% 1.89/2.12  thf('178', plain, ((v2_pre_topc @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('179', plain, ((l1_pre_topc @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('180', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         (~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 1.89/2.12          | (v2_struct_0 @ sk_A)
% 1.89/2.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.89/2.12          | (r3_waybel_9 @ sk_A @ 
% 1.89/2.12             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 1.89/2.12          | ~ (l1_waybel_0 @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 1.89/2.12          | ~ (v7_waybel_0 @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | ~ (v4_orders_2 @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 1.89/2.12      inference('demod', [status(thm)], ['177', '178', '179'])).
% 1.89/2.12  thf('181', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         ((v1_xboole_0 @ sk_B_1)
% 1.89/2.12          | (v2_struct_0 @ sk_A)
% 1.89/2.12          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | ~ (v4_orders_2 @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | ~ (v7_waybel_0 @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | (r3_waybel_9 @ sk_A @ 
% 1.89/2.12             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 1.89/2.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.89/2.12          | (v2_struct_0 @ sk_A)
% 1.89/2.12          | ~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0))),
% 1.89/2.12      inference('sup-', [status(thm)], ['174', '180'])).
% 1.89/2.12  thf('182', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         (~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 1.89/2.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.89/2.12          | (r3_waybel_9 @ sk_A @ 
% 1.89/2.12             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 1.89/2.12          | ~ (v7_waybel_0 @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | ~ (v4_orders_2 @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12          | (v2_struct_0 @ sk_A)
% 1.89/2.12          | (v1_xboole_0 @ sk_B_1))),
% 1.89/2.12      inference('simplify', [status(thm)], ['181'])).
% 1.89/2.12  thf('183', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         ((v1_xboole_0 @ sk_B_1)
% 1.89/2.12          | (v2_struct_0 @ sk_A)
% 1.89/2.12          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12          | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12          | (v2_struct_0 @ sk_A)
% 1.89/2.12          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | ~ (v4_orders_2 @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | (r3_waybel_9 @ sk_A @ 
% 1.89/2.12             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 1.89/2.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.89/2.12          | ~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0))),
% 1.89/2.12      inference('sup-', [status(thm)], ['173', '182'])).
% 1.89/2.12  thf('184', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         (~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 1.89/2.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.89/2.12          | (r3_waybel_9 @ sk_A @ 
% 1.89/2.12             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 1.89/2.12          | ~ (v4_orders_2 @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12          | (v2_struct_0 @ sk_A)
% 1.89/2.12          | (v1_xboole_0 @ sk_B_1))),
% 1.89/2.12      inference('simplify', [status(thm)], ['183'])).
% 1.89/2.12  thf('185', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         ((v1_xboole_0 @ sk_B_1)
% 1.89/2.12          | (v2_struct_0 @ sk_A)
% 1.89/2.12          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12          | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12          | (v2_struct_0 @ sk_A)
% 1.89/2.12          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | (r3_waybel_9 @ sk_A @ 
% 1.89/2.12             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 1.89/2.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.89/2.12          | ~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0))),
% 1.89/2.12      inference('sup-', [status(thm)], ['172', '184'])).
% 1.89/2.12  thf('186', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         (~ (r1_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 1.89/2.12          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.89/2.12          | (r3_waybel_9 @ sk_A @ 
% 1.89/2.12             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 1.89/2.12          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12          | (v2_struct_0 @ sk_A)
% 1.89/2.12          | (v1_xboole_0 @ sk_B_1))),
% 1.89/2.12      inference('simplify', [status(thm)], ['185'])).
% 1.89/2.12  thf('187', plain,
% 1.89/2.12      ((((v1_xboole_0 @ sk_B_1)
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12         | (r3_waybel_9 @ sk_A @ 
% 1.89/2.12            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)
% 1.89/2.12         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))))
% 1.89/2.12         <= (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['171', '186'])).
% 1.89/2.12  thf('188', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('189', plain,
% 1.89/2.12      ((((v1_xboole_0 @ sk_B_1)
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12         | (r3_waybel_9 @ sk_A @ 
% 1.89/2.12            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))
% 1.89/2.12         <= (((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('demod', [status(thm)], ['187', '188'])).
% 1.89/2.12  thf('190', plain,
% 1.89/2.12      ((~ (r3_waybel_9 @ sk_A @ 
% 1.89/2.12           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)))),
% 1.89/2.12      inference('split', [status(esa)], ['0'])).
% 1.89/2.12  thf('191', plain,
% 1.89/2.12      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ sk_B_1)))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['189', '190'])).
% 1.89/2.12  thf('192', plain,
% 1.89/2.12      ((~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 1.89/2.12        | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12        | (v2_struct_0 @ sk_A)
% 1.89/2.12        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12        | ~ (l1_struct_0 @ sk_A))),
% 1.89/2.12      inference('simplify', [status(thm)], ['112'])).
% 1.89/2.12  thf('193', plain,
% 1.89/2.12      ((((v1_xboole_0 @ sk_B_1)
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | ~ (l1_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ sk_B_1)))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['191', '192'])).
% 1.89/2.12  thf('194', plain,
% 1.89/2.12      (((~ (l1_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ sk_B_1)))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('simplify', [status(thm)], ['193'])).
% 1.89/2.12  thf('195', plain,
% 1.89/2.12      (((~ (l1_pre_topc @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ sk_B_1)
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['170', '194'])).
% 1.89/2.12  thf('196', plain, ((l1_pre_topc @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('197', plain,
% 1.89/2.12      ((((v1_xboole_0 @ sk_B_1)
% 1.89/2.12         | (v2_struct_0 @ sk_A)
% 1.89/2.12         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('demod', [status(thm)], ['195', '196'])).
% 1.89/2.12  thf('198', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('199', plain,
% 1.89/2.12      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('clc', [status(thm)], ['197', '198'])).
% 1.89/2.12  thf('200', plain, (~ (v2_struct_0 @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('201', plain,
% 1.89/2.12      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('clc', [status(thm)], ['199', '200'])).
% 1.89/2.12  thf('202', plain,
% 1.89/2.12      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.89/2.12  thf('203', plain,
% 1.89/2.12      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('clc', [status(thm)], ['199', '200'])).
% 1.89/2.12  thf('204', plain,
% 1.89/2.12      (![X0 : $i, X1 : $i]:
% 1.89/2.12         (((X0) = (k4_xboole_0 @ X1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.89/2.12      inference('sup-', [status(thm)], ['130', '131'])).
% 1.89/2.12  thf('205', plain,
% 1.89/2.12      ((![X0 : $i]: ((k2_struct_0 @ sk_A) = (k4_xboole_0 @ X0 @ X0)))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['203', '204'])).
% 1.89/2.12  thf('206', plain,
% 1.89/2.12      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.89/2.12  thf('207', plain,
% 1.89/2.12      ((![X0 : $i]: ((k2_struct_0 @ sk_A) = (k4_xboole_0 @ X0 @ X0)))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['203', '204'])).
% 1.89/2.12  thf('208', plain,
% 1.89/2.12      (![X14 : $i]:
% 1.89/2.12         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 1.89/2.12           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.89/2.12          | ~ (l1_struct_0 @ X14))),
% 1.89/2.12      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.89/2.12  thf('209', plain,
% 1.89/2.12      ((![X0 : $i]:
% 1.89/2.12          ((m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ 
% 1.89/2.12            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.89/2.12           | ~ (l1_struct_0 @ sk_A)))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('sup+', [status(thm)], ['207', '208'])).
% 1.89/2.12  thf('210', plain,
% 1.89/2.12      ((![X0 : $i]:
% 1.89/2.12          (~ (l1_pre_topc @ sk_A)
% 1.89/2.12           | (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ 
% 1.89/2.12              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['206', '209'])).
% 1.89/2.12  thf('211', plain, ((l1_pre_topc @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('212', plain,
% 1.89/2.12      ((![X0 : $i]:
% 1.89/2.12          (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ 
% 1.89/2.12           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('demod', [status(thm)], ['210', '211'])).
% 1.89/2.12  thf('213', plain,
% 1.89/2.12      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.89/2.12         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('sup+', [status(thm)], ['205', '212'])).
% 1.89/2.12  thf('214', plain,
% 1.89/2.12      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.89/2.12         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 1.89/2.12          | ((k7_subset_1 @ X12 @ X11 @ X13) = (k4_xboole_0 @ X11 @ X13)))),
% 1.89/2.12      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.89/2.12  thf('215', plain,
% 1.89/2.12      ((![X0 : $i]:
% 1.89/2.12          ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0)
% 1.89/2.12            = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ X0)))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['213', '214'])).
% 1.89/2.12  thf('216', plain,
% 1.89/2.12      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('clc', [status(thm)], ['199', '200'])).
% 1.89/2.12  thf('217', plain,
% 1.89/2.12      (![X0 : $i, X1 : $i]:
% 1.89/2.12         (((X0) = (k4_xboole_0 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.89/2.12      inference('sup-', [status(thm)], ['146', '147'])).
% 1.89/2.12  thf('218', plain,
% 1.89/2.12      ((![X0 : $i]:
% 1.89/2.12          ((k2_struct_0 @ sk_A) = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ X0)))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['216', '217'])).
% 1.89/2.12  thf('219', plain,
% 1.89/2.12      ((![X0 : $i]:
% 1.89/2.12          ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ X0)
% 1.89/2.12            = (k2_struct_0 @ sk_A)))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('demod', [status(thm)], ['215', '218'])).
% 1.89/2.12  thf('220', plain,
% 1.89/2.12      (![X0 : $i]:
% 1.89/2.12         (~ (l1_struct_0 @ X0)
% 1.89/2.12          | ((k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ 
% 1.89/2.12              (k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ 
% 1.89/2.12               (u1_struct_0 @ X0)))
% 1.89/2.12              = (u1_struct_0 @ X0)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['153', '154'])).
% 1.89/2.12  thf('221', plain,
% 1.89/2.12      (((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('sup+', [status(thm)], ['219', '220'])).
% 1.89/2.12  thf('222', plain,
% 1.89/2.12      (((~ (l1_pre_topc @ sk_A) | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['202', '221'])).
% 1.89/2.12  thf('223', plain, ((l1_pre_topc @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('224', plain,
% 1.89/2.12      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('demod', [status(thm)], ['222', '223'])).
% 1.89/2.12  thf('225', plain,
% 1.89/2.12      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('demod', [status(thm)], ['201', '224'])).
% 1.89/2.12  thf('226', plain,
% 1.89/2.12      (![X16 : $i]:
% 1.89/2.12         (~ (v1_xboole_0 @ (u1_struct_0 @ X16))
% 1.89/2.12          | ~ (l1_struct_0 @ X16)
% 1.89/2.12          | (v2_struct_0 @ X16))),
% 1.89/2.12      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.89/2.12  thf('227', plain,
% 1.89/2.12      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['225', '226'])).
% 1.89/2.12  thf('228', plain, (~ (v2_struct_0 @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('229', plain,
% 1.89/2.12      ((~ (l1_struct_0 @ sk_A))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('clc', [status(thm)], ['227', '228'])).
% 1.89/2.12  thf('230', plain,
% 1.89/2.12      ((~ (l1_pre_topc @ sk_A))
% 1.89/2.12         <= (~
% 1.89/2.12             ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C)) & 
% 1.89/2.12             ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.89/2.12      inference('sup-', [status(thm)], ['169', '229'])).
% 1.89/2.12  thf('231', plain, ((l1_pre_topc @ sk_A)),
% 1.89/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.12  thf('232', plain,
% 1.89/2.12      (~ ((r1_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) | 
% 1.89/2.12       ((r3_waybel_9 @ sk_A @ 
% 1.89/2.12         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_C))),
% 1.89/2.12      inference('demod', [status(thm)], ['230', '231'])).
% 1.89/2.12  thf('233', plain, ($false),
% 1.89/2.12      inference('sat_resolution*', [status(thm)], ['1', '167', '168', '232'])).
% 1.89/2.12  
% 1.89/2.12  % SZS output end Refutation
% 1.89/2.12  
% 1.98/2.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
