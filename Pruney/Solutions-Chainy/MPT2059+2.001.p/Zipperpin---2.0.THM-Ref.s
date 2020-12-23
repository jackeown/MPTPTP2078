%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dqXgoZGZHC

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:52 EST 2020

% Result     : Theorem 0.97s
% Output     : Refutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :  241 ( 668 expanded)
%              Number of leaves         :   45 ( 224 expanded)
%              Depth                    :   31
%              Number of atoms          : 3195 (13487 expanded)
%              Number of equality atoms :   35 ( 158 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t18_yellow19,conjecture,(
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
             => ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) )
              <=> ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) )).

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
               => ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) )
                <=> ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_yellow19])).

thf('0',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
    | ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
    | ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('8',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v1_xboole_0 @ X24 )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( v2_waybel_0 @ X26 @ ( k3_yellow_1 @ X24 ) )
      | ~ ( v13_waybel_0 @ X26 @ ( k3_yellow_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X24 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X25 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('11',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('12',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('13',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('14',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v1_xboole_0 @ X24 )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( v2_waybel_0 @ X26 @ ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) )
      | ~ ( v13_waybel_0 @ X26 @ ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X25 @ X24 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('18',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('21',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['15','18','21'])).

thf('23',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','22'])).

thf('24',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('29',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('31',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v1_xboole_0 @ X27 )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 )
      | ( v1_xboole_0 @ X29 )
      | ~ ( v1_subset_1 @ X29 @ ( u1_struct_0 @ ( k3_yellow_1 @ X27 ) ) )
      | ~ ( v2_waybel_0 @ X29 @ ( k3_yellow_1 @ X27 ) )
      | ~ ( v13_waybel_0 @ X29 @ ( k3_yellow_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X27 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X28 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('32',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('33',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('34',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('35',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('36',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v1_xboole_0 @ X27 )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 )
      | ( v1_xboole_0 @ X29 )
      | ~ ( v1_subset_1 @ X29 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) )
      | ~ ( v2_waybel_0 @ X29 @ ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) )
      | ~ ( v13_waybel_0 @ X29 @ ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X28 @ X27 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
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
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('39',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('40',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('42',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','42'])).

thf('44',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','43'])).

thf('45',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('51',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('52',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_xboole_0 @ X21 )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( v2_waybel_0 @ X23 @ ( k3_yellow_1 @ X21 ) )
      | ~ ( v13_waybel_0 @ X23 @ ( k3_yellow_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X21 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X22 @ X21 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('53',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('54',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('55',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('56',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_xboole_0 @ X21 )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( v2_waybel_0 @ X23 @ ( k3_lattice3 @ ( k1_lattice3 @ X21 ) ) )
      | ~ ( v13_waybel_0 @ X23 @ ( k3_lattice3 @ ( k1_lattice3 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X21 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X22 @ X21 @ X23 ) @ X22 ) ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('59',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','60'])).

thf('62',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['66'])).

thf(t13_yellow19,axiom,(
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
             => ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) )
              <=> ( r2_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) )).

thf('68',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v4_orders_2 @ X30 )
      | ~ ( v7_waybel_0 @ X30 )
      | ~ ( l1_waybel_0 @ X30 @ X31 )
      | ~ ( r2_hidden @ X32 @ ( k10_yellow_6 @ X31 @ X30 ) )
      | ( r2_waybel_7 @ X31 @ ( k2_yellow19 @ X31 @ X30 ) @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow19])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_C_1 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_C_1 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('75',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('76',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( v1_subset_1 @ X33 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X34 ) ) ) )
      | ~ ( v2_waybel_0 @ X33 @ ( k3_yellow_1 @ ( k2_struct_0 @ X34 ) ) )
      | ~ ( v13_waybel_0 @ X33 @ ( k3_yellow_1 @ ( k2_struct_0 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X34 ) ) ) ) )
      | ( X33
        = ( k2_yellow19 @ X34 @ ( k3_yellow19 @ X34 @ ( k2_struct_0 @ X34 ) @ X33 ) ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('77',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('78',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('79',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('80',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('81',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( v1_subset_1 @ X33 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X34 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X33 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X34 ) ) ) )
      | ~ ( v13_waybel_0 @ X33 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X34 ) ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X34 ) ) ) ) ) )
      | ( X33
        = ( k2_yellow19 @ X34 @ ( k3_yellow19 @ X34 @ ( k2_struct_0 @ X34 ) @ X33 ) ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['75','81'])).

thf('83',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('84',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('85',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( sk_B_1
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['73','93'])).

thf('95',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['65','94'])).

thf('96',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['48','96'])).

thf('98',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['27','98'])).

thf('100',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('102',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('103',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_xboole_0 @ X21 )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( v2_waybel_0 @ X23 @ ( k3_yellow_1 @ X21 ) )
      | ~ ( v13_waybel_0 @ X23 @ ( k3_yellow_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X21 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X22 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('104',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('105',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('106',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('107',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_xboole_0 @ X21 )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( v2_waybel_0 @ X23 @ ( k3_lattice3 @ ( k1_lattice3 @ X21 ) ) )
      | ~ ( v13_waybel_0 @ X23 @ ( k3_lattice3 @ ( k1_lattice3 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X21 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X22 @ X21 @ X23 ) ) ) ),
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
      | ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['100','113'])).

thf('115',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['4','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
   <= ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('120',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
      & ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
      & ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
      & ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
      & ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['3','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) )).

thf('127',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( r2_hidden @ X18 @ ( k1_connsp_2 @ X19 @ X18 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k1_connsp_2 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( k1_connsp_2 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    r2_hidden @ sk_C_1 @ ( k1_connsp_2 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('135',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('136',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('142',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('143',plain,(
    r1_tarski @ ( k1_connsp_2 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('144',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['133','145'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('148',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
      & ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['125','148'])).

thf('150',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
      & ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','149'])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
    | ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['66'])).

thf('154',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('155',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('156',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('157',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
   <= ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['66'])).

thf('158',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('159',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('160',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('161',plain,
    ( sk_B_1
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('162',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v4_orders_2 @ X30 )
      | ~ ( v7_waybel_0 @ X30 )
      | ~ ( l1_waybel_0 @ X30 @ X31 )
      | ~ ( r2_waybel_7 @ X31 @ ( k2_yellow19 @ X31 @ X30 ) @ X32 )
      | ( r2_hidden @ X32 @ ( k10_yellow_6 @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow19])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['160','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['159','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['158','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['157','172'])).

thf('174',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('177',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,
    ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['112'])).

thf('179',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['156','180'])).

thf('182',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['185','186'])).

thf('188',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['155','187'])).

thf('189',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('190',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['188','189'])).

thf('191',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['154','190'])).

thf('192',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1 )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','152','153','193'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dqXgoZGZHC
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:02:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.97/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.97/1.17  % Solved by: fo/fo7.sh
% 0.97/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.97/1.17  % done 1065 iterations in 0.706s
% 0.97/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.97/1.17  % SZS output start Refutation
% 0.97/1.17  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.97/1.17  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.97/1.17  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.97/1.17  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.97/1.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.97/1.17  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.97/1.17  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.97/1.17  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.97/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.97/1.17  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.97/1.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.97/1.17  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.97/1.17  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.97/1.17  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.97/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.97/1.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.97/1.17  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.97/1.17  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.97/1.17  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.97/1.17  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.97/1.17  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.97/1.17  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.97/1.17  thf(r2_waybel_7_type, type, r2_waybel_7: $i > $i > $i > $o).
% 0.97/1.17  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.97/1.17  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.97/1.17  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.97/1.17  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.97/1.17  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.97/1.17  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.97/1.17  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.97/1.17  thf(t18_yellow19, conjecture,
% 0.97/1.17    (![A:$i]:
% 0.97/1.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.97/1.17       ( ![B:$i]:
% 0.97/1.17         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.97/1.17             ( v1_subset_1 @
% 0.97/1.17               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.97/1.17             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.97/1.17             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.97/1.17             ( m1_subset_1 @
% 0.97/1.17               B @ 
% 0.97/1.17               ( k1_zfmisc_1 @
% 0.97/1.17                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.97/1.17           ( ![C:$i]:
% 0.97/1.17             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.97/1.17               ( ( r2_hidden @
% 0.97/1.17                   C @ 
% 0.97/1.17                   ( k10_yellow_6 @
% 0.97/1.17                     A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) <=>
% 0.97/1.17                 ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.97/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.97/1.17    (~( ![A:$i]:
% 0.97/1.17        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.97/1.17            ( l1_pre_topc @ A ) ) =>
% 0.97/1.17          ( ![B:$i]:
% 0.97/1.17            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.97/1.17                ( v1_subset_1 @
% 0.97/1.17                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.97/1.17                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.97/1.17                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.97/1.17                ( m1_subset_1 @
% 0.97/1.17                  B @ 
% 0.97/1.17                  ( k1_zfmisc_1 @
% 0.97/1.17                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.97/1.17              ( ![C:$i]:
% 0.97/1.17                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.97/1.17                  ( ( r2_hidden @
% 0.97/1.17                      C @ 
% 0.97/1.17                      ( k10_yellow_6 @
% 0.97/1.17                        A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) <=>
% 0.97/1.17                    ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.97/1.17    inference('cnf.neg', [status(esa)], [t18_yellow19])).
% 0.97/1.17  thf('0', plain,
% 0.97/1.17      ((~ (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)
% 0.97/1.17        | ~ (r2_hidden @ sk_C_1 @ 
% 0.97/1.17             (k10_yellow_6 @ sk_A @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('1', plain,
% 0.97/1.17      (~ ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)) | 
% 0.97/1.17       ~
% 0.97/1.17       ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17         (k10_yellow_6 @ sk_A @ 
% 0.97/1.17          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.97/1.17      inference('split', [status(esa)], ['0'])).
% 0.97/1.17  thf(dt_l1_pre_topc, axiom,
% 0.97/1.17    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.97/1.17  thf('2', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.97/1.17      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.97/1.17  thf(d3_struct_0, axiom,
% 0.97/1.17    (![A:$i]:
% 0.97/1.17     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.97/1.17  thf('3', plain,
% 0.97/1.17      (![X13 : $i]:
% 0.97/1.17         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.97/1.17      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.97/1.17  thf('4', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.97/1.17      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.97/1.17  thf('5', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.97/1.17      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.97/1.17  thf(dt_k2_struct_0, axiom,
% 0.97/1.17    (![A:$i]:
% 0.97/1.17     ( ( l1_struct_0 @ A ) =>
% 0.97/1.17       ( m1_subset_1 @
% 0.97/1.17         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.97/1.17  thf('6', plain,
% 0.97/1.17      (![X14 : $i]:
% 0.97/1.17         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 0.97/1.17           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.97/1.17          | ~ (l1_struct_0 @ X14))),
% 0.97/1.17      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.97/1.17  thf('7', plain,
% 0.97/1.17      ((m1_subset_1 @ sk_B_1 @ 
% 0.97/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf(d2_yellow_1, axiom,
% 0.97/1.17    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.97/1.17  thf('8', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('9', plain,
% 0.97/1.17      ((m1_subset_1 @ sk_B_1 @ 
% 0.97/1.17        (k1_zfmisc_1 @ 
% 0.97/1.17         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.97/1.17      inference('demod', [status(thm)], ['7', '8'])).
% 0.97/1.17  thf(fc4_yellow19, axiom,
% 0.97/1.17    (![A:$i,B:$i,C:$i]:
% 0.97/1.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.97/1.17         ( ~( v1_xboole_0 @ B ) ) & 
% 0.97/1.17         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.97/1.17         ( ~( v1_xboole_0 @ C ) ) & 
% 0.97/1.17         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.97/1.17         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.97/1.17         ( m1_subset_1 @
% 0.97/1.17           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.97/1.17       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.97/1.17         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.97/1.17         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.97/1.17         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.97/1.17  thf('10', plain,
% 0.97/1.17      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.97/1.17          | (v1_xboole_0 @ X24)
% 0.97/1.17          | ~ (l1_struct_0 @ X25)
% 0.97/1.17          | (v2_struct_0 @ X25)
% 0.97/1.17          | (v1_xboole_0 @ X26)
% 0.97/1.17          | ~ (v2_waybel_0 @ X26 @ (k3_yellow_1 @ X24))
% 0.97/1.17          | ~ (v13_waybel_0 @ X26 @ (k3_yellow_1 @ X24))
% 0.97/1.17          | ~ (m1_subset_1 @ X26 @ 
% 0.97/1.17               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X24))))
% 0.97/1.17          | (v4_orders_2 @ (k3_yellow19 @ X25 @ X24 @ X26)))),
% 0.97/1.17      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.97/1.17  thf('11', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('12', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('13', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('14', plain,
% 0.97/1.17      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.97/1.17          | (v1_xboole_0 @ X24)
% 0.97/1.17          | ~ (l1_struct_0 @ X25)
% 0.97/1.17          | (v2_struct_0 @ X25)
% 0.97/1.17          | (v1_xboole_0 @ X26)
% 0.97/1.17          | ~ (v2_waybel_0 @ X26 @ (k3_lattice3 @ (k1_lattice3 @ X24)))
% 0.97/1.17          | ~ (v13_waybel_0 @ X26 @ (k3_lattice3 @ (k1_lattice3 @ X24)))
% 0.97/1.17          | ~ (m1_subset_1 @ X26 @ 
% 0.97/1.17               (k1_zfmisc_1 @ 
% 0.97/1.17                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X24)))))
% 0.97/1.17          | (v4_orders_2 @ (k3_yellow19 @ X25 @ X24 @ X26)))),
% 0.97/1.17      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.97/1.17  thf('15', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.97/1.17               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.97/1.17          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.97/1.17               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.97/1.17          | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17          | (v2_struct_0 @ X0)
% 0.97/1.17          | ~ (l1_struct_0 @ X0)
% 0.97/1.17          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.97/1.17               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.97/1.17      inference('sup-', [status(thm)], ['9', '14'])).
% 0.97/1.17  thf('16', plain,
% 0.97/1.17      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('17', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('18', plain,
% 0.97/1.17      ((v13_waybel_0 @ sk_B_1 @ 
% 0.97/1.17        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.97/1.17      inference('demod', [status(thm)], ['16', '17'])).
% 0.97/1.17  thf('19', plain,
% 0.97/1.17      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('20', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('21', plain,
% 0.97/1.17      ((v2_waybel_0 @ sk_B_1 @ 
% 0.97/1.17        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.97/1.17      inference('demod', [status(thm)], ['19', '20'])).
% 0.97/1.17  thf('22', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17          | (v2_struct_0 @ X0)
% 0.97/1.17          | ~ (l1_struct_0 @ X0)
% 0.97/1.17          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.97/1.17               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.97/1.17      inference('demod', [status(thm)], ['15', '18', '21'])).
% 0.97/1.17  thf('23', plain,
% 0.97/1.17      ((~ (l1_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17        | ~ (l1_struct_0 @ sk_A)
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['6', '22'])).
% 0.97/1.17  thf('24', plain,
% 0.97/1.17      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17        | ~ (l1_struct_0 @ sk_A))),
% 0.97/1.17      inference('simplify', [status(thm)], ['23'])).
% 0.97/1.17  thf('25', plain,
% 0.97/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['5', '24'])).
% 0.97/1.17  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('27', plain,
% 0.97/1.17      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.97/1.17      inference('demod', [status(thm)], ['25', '26'])).
% 0.97/1.17  thf('28', plain,
% 0.97/1.17      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.97/1.17      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.97/1.17  thf('29', plain,
% 0.97/1.17      (![X14 : $i]:
% 0.97/1.17         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 0.97/1.17           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.97/1.17          | ~ (l1_struct_0 @ X14))),
% 0.97/1.17      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.97/1.17  thf('30', plain,
% 0.97/1.17      ((m1_subset_1 @ sk_B_1 @ 
% 0.97/1.17        (k1_zfmisc_1 @ 
% 0.97/1.17         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.97/1.17      inference('demod', [status(thm)], ['7', '8'])).
% 0.97/1.17  thf(fc5_yellow19, axiom,
% 0.97/1.17    (![A:$i,B:$i,C:$i]:
% 0.97/1.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.97/1.17         ( ~( v1_xboole_0 @ B ) ) & 
% 0.97/1.17         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.97/1.17         ( ~( v1_xboole_0 @ C ) ) & 
% 0.97/1.17         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.97/1.17         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.97/1.17         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.97/1.17         ( m1_subset_1 @
% 0.97/1.17           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.97/1.17       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.97/1.17         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.97/1.17         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.97/1.17  thf('31', plain,
% 0.97/1.17      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.97/1.17          | (v1_xboole_0 @ X27)
% 0.97/1.17          | ~ (l1_struct_0 @ X28)
% 0.97/1.17          | (v2_struct_0 @ X28)
% 0.97/1.17          | (v1_xboole_0 @ X29)
% 0.97/1.17          | ~ (v1_subset_1 @ X29 @ (u1_struct_0 @ (k3_yellow_1 @ X27)))
% 0.97/1.17          | ~ (v2_waybel_0 @ X29 @ (k3_yellow_1 @ X27))
% 0.97/1.17          | ~ (v13_waybel_0 @ X29 @ (k3_yellow_1 @ X27))
% 0.97/1.17          | ~ (m1_subset_1 @ X29 @ 
% 0.97/1.17               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X27))))
% 0.97/1.17          | (v7_waybel_0 @ (k3_yellow19 @ X28 @ X27 @ X29)))),
% 0.97/1.17      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.97/1.17  thf('32', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('33', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('34', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('35', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('36', plain,
% 0.97/1.17      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.97/1.17          | (v1_xboole_0 @ X27)
% 0.97/1.17          | ~ (l1_struct_0 @ X28)
% 0.97/1.17          | (v2_struct_0 @ X28)
% 0.97/1.17          | (v1_xboole_0 @ X29)
% 0.97/1.17          | ~ (v1_subset_1 @ X29 @ 
% 0.97/1.17               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X27))))
% 0.97/1.17          | ~ (v2_waybel_0 @ X29 @ (k3_lattice3 @ (k1_lattice3 @ X27)))
% 0.97/1.17          | ~ (v13_waybel_0 @ X29 @ (k3_lattice3 @ (k1_lattice3 @ X27)))
% 0.97/1.17          | ~ (m1_subset_1 @ X29 @ 
% 0.97/1.17               (k1_zfmisc_1 @ 
% 0.97/1.17                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X27)))))
% 0.97/1.17          | (v7_waybel_0 @ (k3_yellow19 @ X28 @ X27 @ X29)))),
% 0.97/1.17      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.97/1.17  thf('37', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.97/1.17               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.97/1.17          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.97/1.17               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.97/1.17          | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.97/1.17               (u1_struct_0 @ 
% 0.97/1.17                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.97/1.17          | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17          | (v2_struct_0 @ X0)
% 0.97/1.17          | ~ (l1_struct_0 @ X0)
% 0.97/1.17          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.97/1.17               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.97/1.17      inference('sup-', [status(thm)], ['30', '36'])).
% 0.97/1.17  thf('38', plain,
% 0.97/1.17      ((v13_waybel_0 @ sk_B_1 @ 
% 0.97/1.17        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.97/1.17      inference('demod', [status(thm)], ['16', '17'])).
% 0.97/1.17  thf('39', plain,
% 0.97/1.17      ((v2_waybel_0 @ sk_B_1 @ 
% 0.97/1.17        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.97/1.17      inference('demod', [status(thm)], ['19', '20'])).
% 0.97/1.17  thf('40', plain,
% 0.97/1.17      ((v1_subset_1 @ sk_B_1 @ 
% 0.97/1.17        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('41', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('42', plain,
% 0.97/1.17      ((v1_subset_1 @ sk_B_1 @ 
% 0.97/1.17        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.97/1.17      inference('demod', [status(thm)], ['40', '41'])).
% 0.97/1.17  thf('43', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17          | (v2_struct_0 @ X0)
% 0.97/1.17          | ~ (l1_struct_0 @ X0)
% 0.97/1.17          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.97/1.17               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.97/1.17      inference('demod', [status(thm)], ['37', '38', '39', '42'])).
% 0.97/1.17  thf('44', plain,
% 0.97/1.17      ((~ (l1_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17        | ~ (l1_struct_0 @ sk_A)
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['29', '43'])).
% 0.97/1.17  thf('45', plain,
% 0.97/1.17      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17        | ~ (l1_struct_0 @ sk_A))),
% 0.97/1.17      inference('simplify', [status(thm)], ['44'])).
% 0.97/1.17  thf('46', plain,
% 0.97/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['28', '45'])).
% 0.97/1.17  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('48', plain,
% 0.97/1.17      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.97/1.17      inference('demod', [status(thm)], ['46', '47'])).
% 0.97/1.17  thf('49', plain,
% 0.97/1.17      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.97/1.17      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.97/1.17  thf('50', plain,
% 0.97/1.17      (![X14 : $i]:
% 0.97/1.17         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 0.97/1.17           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.97/1.17          | ~ (l1_struct_0 @ X14))),
% 0.97/1.17      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.97/1.17  thf('51', plain,
% 0.97/1.17      ((m1_subset_1 @ sk_B_1 @ 
% 0.97/1.17        (k1_zfmisc_1 @ 
% 0.97/1.17         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.97/1.17      inference('demod', [status(thm)], ['7', '8'])).
% 0.97/1.17  thf(dt_k3_yellow19, axiom,
% 0.97/1.17    (![A:$i,B:$i,C:$i]:
% 0.97/1.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.97/1.17         ( ~( v1_xboole_0 @ B ) ) & 
% 0.97/1.17         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.97/1.17         ( ~( v1_xboole_0 @ C ) ) & 
% 0.97/1.17         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.97/1.17         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.97/1.17         ( m1_subset_1 @
% 0.97/1.17           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.97/1.17       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.97/1.17         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.97/1.17         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.97/1.17  thf('52', plain,
% 0.97/1.17      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.97/1.17          | (v1_xboole_0 @ X21)
% 0.97/1.17          | ~ (l1_struct_0 @ X22)
% 0.97/1.17          | (v2_struct_0 @ X22)
% 0.97/1.17          | (v1_xboole_0 @ X23)
% 0.97/1.17          | ~ (v2_waybel_0 @ X23 @ (k3_yellow_1 @ X21))
% 0.97/1.17          | ~ (v13_waybel_0 @ X23 @ (k3_yellow_1 @ X21))
% 0.97/1.17          | ~ (m1_subset_1 @ X23 @ 
% 0.97/1.17               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X21))))
% 0.97/1.17          | (l1_waybel_0 @ (k3_yellow19 @ X22 @ X21 @ X23) @ X22))),
% 0.97/1.17      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.97/1.17  thf('53', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('54', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('55', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('56', plain,
% 0.97/1.17      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.97/1.17          | (v1_xboole_0 @ X21)
% 0.97/1.17          | ~ (l1_struct_0 @ X22)
% 0.97/1.17          | (v2_struct_0 @ X22)
% 0.97/1.17          | (v1_xboole_0 @ X23)
% 0.97/1.17          | ~ (v2_waybel_0 @ X23 @ (k3_lattice3 @ (k1_lattice3 @ X21)))
% 0.97/1.17          | ~ (v13_waybel_0 @ X23 @ (k3_lattice3 @ (k1_lattice3 @ X21)))
% 0.97/1.17          | ~ (m1_subset_1 @ X23 @ 
% 0.97/1.17               (k1_zfmisc_1 @ 
% 0.97/1.17                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X21)))))
% 0.97/1.17          | (l1_waybel_0 @ (k3_yellow19 @ X22 @ X21 @ X23) @ X22))),
% 0.97/1.17      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.97/1.17  thf('57', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.97/1.17           X0)
% 0.97/1.17          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.97/1.17               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.97/1.17          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.97/1.17               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.97/1.17          | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17          | (v2_struct_0 @ X0)
% 0.97/1.17          | ~ (l1_struct_0 @ X0)
% 0.97/1.17          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.97/1.17               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.97/1.17      inference('sup-', [status(thm)], ['51', '56'])).
% 0.97/1.17  thf('58', plain,
% 0.97/1.17      ((v13_waybel_0 @ sk_B_1 @ 
% 0.97/1.17        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.97/1.17      inference('demod', [status(thm)], ['16', '17'])).
% 0.97/1.17  thf('59', plain,
% 0.97/1.17      ((v2_waybel_0 @ sk_B_1 @ 
% 0.97/1.17        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.97/1.17      inference('demod', [status(thm)], ['19', '20'])).
% 0.97/1.17  thf('60', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.97/1.17           X0)
% 0.97/1.17          | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17          | (v2_struct_0 @ X0)
% 0.97/1.17          | ~ (l1_struct_0 @ X0)
% 0.97/1.17          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.97/1.17               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.97/1.17      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.97/1.17  thf('61', plain,
% 0.97/1.17      ((~ (l1_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17        | ~ (l1_struct_0 @ sk_A)
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | (l1_waybel_0 @ 
% 0.97/1.17           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.97/1.17      inference('sup-', [status(thm)], ['50', '60'])).
% 0.97/1.17  thf('62', plain,
% 0.97/1.17      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.97/1.17         sk_A)
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17        | ~ (l1_struct_0 @ sk_A))),
% 0.97/1.17      inference('simplify', [status(thm)], ['61'])).
% 0.97/1.17  thf('63', plain,
% 0.97/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | (l1_waybel_0 @ 
% 0.97/1.17           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.97/1.17      inference('sup-', [status(thm)], ['49', '62'])).
% 0.97/1.17  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('65', plain,
% 0.97/1.17      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | (l1_waybel_0 @ 
% 0.97/1.17           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.97/1.17      inference('demod', [status(thm)], ['63', '64'])).
% 0.97/1.17  thf('66', plain,
% 0.97/1.17      (((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)
% 0.97/1.17        | (r2_hidden @ sk_C_1 @ 
% 0.97/1.17           (k10_yellow_6 @ sk_A @ 
% 0.97/1.17            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('67', plain,
% 0.97/1.17      (((r2_hidden @ sk_C_1 @ 
% 0.97/1.17         (k10_yellow_6 @ sk_A @ 
% 0.97/1.17          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 0.97/1.17         <= (((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('split', [status(esa)], ['66'])).
% 0.97/1.17  thf(t13_yellow19, axiom,
% 0.97/1.17    (![A:$i]:
% 0.97/1.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.97/1.17       ( ![B:$i]:
% 0.97/1.17         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.97/1.17             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.97/1.17           ( ![C:$i]:
% 0.97/1.17             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.97/1.17               ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) <=>
% 0.97/1.17                 ( r2_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.97/1.17  thf('68', plain,
% 0.97/1.17      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.97/1.17         ((v2_struct_0 @ X30)
% 0.97/1.17          | ~ (v4_orders_2 @ X30)
% 0.97/1.17          | ~ (v7_waybel_0 @ X30)
% 0.97/1.17          | ~ (l1_waybel_0 @ X30 @ X31)
% 0.97/1.17          | ~ (r2_hidden @ X32 @ (k10_yellow_6 @ X31 @ X30))
% 0.97/1.17          | (r2_waybel_7 @ X31 @ (k2_yellow19 @ X31 @ X30) @ X32)
% 0.97/1.17          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 0.97/1.17          | ~ (l1_pre_topc @ X31)
% 0.97/1.17          | ~ (v2_pre_topc @ X31)
% 0.97/1.17          | (v2_struct_0 @ X31))),
% 0.97/1.17      inference('cnf', [status(esa)], [t13_yellow19])).
% 0.97/1.17  thf('69', plain,
% 0.97/1.17      ((((v2_struct_0 @ sk_A)
% 0.97/1.17         | ~ (v2_pre_topc @ sk_A)
% 0.97/1.17         | ~ (l1_pre_topc @ sk_A)
% 0.97/1.17         | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.97/1.17         | (r2_waybel_7 @ sk_A @ 
% 0.97/1.17            (k2_yellow19 @ sk_A @ 
% 0.97/1.17             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.97/1.17            sk_C_1)
% 0.97/1.17         | ~ (l1_waybel_0 @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.97/1.17         | ~ (v7_waybel_0 @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | ~ (v4_orders_2 @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 0.97/1.17         <= (((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('sup-', [status(thm)], ['67', '68'])).
% 0.97/1.17  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('72', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('73', plain,
% 0.97/1.17      ((((v2_struct_0 @ sk_A)
% 0.97/1.17         | (r2_waybel_7 @ sk_A @ 
% 0.97/1.17            (k2_yellow19 @ sk_A @ 
% 0.97/1.17             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.97/1.17            sk_C_1)
% 0.97/1.17         | ~ (l1_waybel_0 @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.97/1.17         | ~ (v7_waybel_0 @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | ~ (v4_orders_2 @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 0.97/1.17         <= (((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.97/1.17  thf('74', plain,
% 0.97/1.17      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.97/1.17      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.97/1.17  thf('75', plain,
% 0.97/1.17      ((m1_subset_1 @ sk_B_1 @ 
% 0.97/1.17        (k1_zfmisc_1 @ 
% 0.97/1.17         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.97/1.17      inference('demod', [status(thm)], ['7', '8'])).
% 0.97/1.17  thf(t15_yellow19, axiom,
% 0.97/1.17    (![A:$i]:
% 0.97/1.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.97/1.17       ( ![B:$i]:
% 0.97/1.17         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.97/1.17             ( v1_subset_1 @
% 0.97/1.17               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.97/1.17             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.97/1.17             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.97/1.17             ( m1_subset_1 @
% 0.97/1.17               B @ 
% 0.97/1.17               ( k1_zfmisc_1 @
% 0.97/1.17                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.97/1.17           ( ( B ) =
% 0.97/1.17             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.97/1.17  thf('76', plain,
% 0.97/1.17      (![X33 : $i, X34 : $i]:
% 0.97/1.17         ((v1_xboole_0 @ X33)
% 0.97/1.17          | ~ (v1_subset_1 @ X33 @ 
% 0.97/1.17               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X34))))
% 0.97/1.17          | ~ (v2_waybel_0 @ X33 @ (k3_yellow_1 @ (k2_struct_0 @ X34)))
% 0.97/1.17          | ~ (v13_waybel_0 @ X33 @ (k3_yellow_1 @ (k2_struct_0 @ X34)))
% 0.97/1.17          | ~ (m1_subset_1 @ X33 @ 
% 0.97/1.17               (k1_zfmisc_1 @ 
% 0.97/1.17                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X34)))))
% 0.97/1.17          | ((X33)
% 0.97/1.17              = (k2_yellow19 @ X34 @ 
% 0.97/1.17                 (k3_yellow19 @ X34 @ (k2_struct_0 @ X34) @ X33)))
% 0.97/1.17          | ~ (l1_struct_0 @ X34)
% 0.97/1.17          | (v2_struct_0 @ X34))),
% 0.97/1.17      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.97/1.17  thf('77', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('78', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('79', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('80', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('81', plain,
% 0.97/1.17      (![X33 : $i, X34 : $i]:
% 0.97/1.17         ((v1_xboole_0 @ X33)
% 0.97/1.17          | ~ (v1_subset_1 @ X33 @ 
% 0.97/1.17               (u1_struct_0 @ 
% 0.97/1.17                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X34)))))
% 0.97/1.17          | ~ (v2_waybel_0 @ X33 @ 
% 0.97/1.17               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X34))))
% 0.97/1.17          | ~ (v13_waybel_0 @ X33 @ 
% 0.97/1.17               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X34))))
% 0.97/1.17          | ~ (m1_subset_1 @ X33 @ 
% 0.97/1.17               (k1_zfmisc_1 @ 
% 0.97/1.17                (u1_struct_0 @ 
% 0.97/1.17                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X34))))))
% 0.97/1.17          | ((X33)
% 0.97/1.17              = (k2_yellow19 @ X34 @ 
% 0.97/1.17                 (k3_yellow19 @ X34 @ (k2_struct_0 @ X34) @ X33)))
% 0.97/1.17          | ~ (l1_struct_0 @ X34)
% 0.97/1.17          | (v2_struct_0 @ X34))),
% 0.97/1.17      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 0.97/1.17  thf('82', plain,
% 0.97/1.17      (((v2_struct_0 @ sk_A)
% 0.97/1.17        | ~ (l1_struct_0 @ sk_A)
% 0.97/1.17        | ((sk_B_1)
% 0.97/1.17            = (k2_yellow19 @ sk_A @ 
% 0.97/1.17               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.97/1.17        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.97/1.17             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.97/1.17        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.97/1.17             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.97/1.17        | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.97/1.17             (u1_struct_0 @ 
% 0.97/1.17              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1))),
% 0.97/1.17      inference('sup-', [status(thm)], ['75', '81'])).
% 0.97/1.17  thf('83', plain,
% 0.97/1.17      ((v13_waybel_0 @ sk_B_1 @ 
% 0.97/1.17        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.97/1.17      inference('demod', [status(thm)], ['16', '17'])).
% 0.97/1.17  thf('84', plain,
% 0.97/1.17      ((v2_waybel_0 @ sk_B_1 @ 
% 0.97/1.17        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.97/1.17      inference('demod', [status(thm)], ['19', '20'])).
% 0.97/1.17  thf('85', plain,
% 0.97/1.17      ((v1_subset_1 @ sk_B_1 @ 
% 0.97/1.17        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.97/1.17      inference('demod', [status(thm)], ['40', '41'])).
% 0.97/1.17  thf('86', plain,
% 0.97/1.17      (((v2_struct_0 @ sk_A)
% 0.97/1.17        | ~ (l1_struct_0 @ sk_A)
% 0.97/1.17        | ((sk_B_1)
% 0.97/1.17            = (k2_yellow19 @ sk_A @ 
% 0.97/1.17               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1))),
% 0.97/1.17      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 0.97/1.17  thf('87', plain,
% 0.97/1.17      ((~ (l1_pre_topc @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | ((sk_B_1)
% 0.97/1.17            = (k2_yellow19 @ sk_A @ 
% 0.97/1.17               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.97/1.17        | (v2_struct_0 @ sk_A))),
% 0.97/1.17      inference('sup-', [status(thm)], ['74', '86'])).
% 0.97/1.17  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('89', plain,
% 0.97/1.17      (((v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | ((sk_B_1)
% 0.97/1.17            = (k2_yellow19 @ sk_A @ 
% 0.97/1.17               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.97/1.17        | (v2_struct_0 @ sk_A))),
% 0.97/1.17      inference('demod', [status(thm)], ['87', '88'])).
% 0.97/1.17  thf('90', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('91', plain,
% 0.97/1.17      (((v2_struct_0 @ sk_A)
% 0.97/1.17        | ((sk_B_1)
% 0.97/1.17            = (k2_yellow19 @ sk_A @ 
% 0.97/1.17               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.97/1.17      inference('clc', [status(thm)], ['89', '90'])).
% 0.97/1.17  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('93', plain,
% 0.97/1.17      (((sk_B_1)
% 0.97/1.17         = (k2_yellow19 @ sk_A @ 
% 0.97/1.17            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.97/1.17      inference('clc', [status(thm)], ['91', '92'])).
% 0.97/1.17  thf('94', plain,
% 0.97/1.17      ((((v2_struct_0 @ sk_A)
% 0.97/1.17         | (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)
% 0.97/1.17         | ~ (l1_waybel_0 @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.97/1.17         | ~ (v7_waybel_0 @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | ~ (v4_orders_2 @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 0.97/1.17         <= (((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('demod', [status(thm)], ['73', '93'])).
% 0.97/1.17  thf('95', plain,
% 0.97/1.17      ((((v1_xboole_0 @ sk_B_1)
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | ~ (v4_orders_2 @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | ~ (v7_waybel_0 @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)
% 0.97/1.17         | (v2_struct_0 @ sk_A)))
% 0.97/1.17         <= (((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('sup-', [status(thm)], ['65', '94'])).
% 0.97/1.17  thf('96', plain,
% 0.97/1.17      ((((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)
% 0.97/1.17         | ~ (v7_waybel_0 @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | ~ (v4_orders_2 @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ sk_B_1)))
% 0.97/1.17         <= (((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('simplify', [status(thm)], ['95'])).
% 0.97/1.17  thf('97', plain,
% 0.97/1.17      ((((v1_xboole_0 @ sk_B_1)
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | ~ (v4_orders_2 @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)))
% 0.97/1.17         <= (((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('sup-', [status(thm)], ['48', '96'])).
% 0.97/1.17  thf('98', plain,
% 0.97/1.17      ((((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)
% 0.97/1.17         | ~ (v4_orders_2 @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ sk_B_1)))
% 0.97/1.17         <= (((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('simplify', [status(thm)], ['97'])).
% 0.97/1.17  thf('99', plain,
% 0.97/1.17      ((((v1_xboole_0 @ sk_B_1)
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)))
% 0.97/1.17         <= (((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('sup-', [status(thm)], ['27', '98'])).
% 0.97/1.17  thf('100', plain,
% 0.97/1.17      ((((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)
% 0.97/1.17         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ sk_B_1)))
% 0.97/1.17         <= (((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('simplify', [status(thm)], ['99'])).
% 0.97/1.17  thf('101', plain,
% 0.97/1.17      (![X14 : $i]:
% 0.97/1.17         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 0.97/1.17           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.97/1.17          | ~ (l1_struct_0 @ X14))),
% 0.97/1.17      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.97/1.17  thf('102', plain,
% 0.97/1.17      ((m1_subset_1 @ sk_B_1 @ 
% 0.97/1.17        (k1_zfmisc_1 @ 
% 0.97/1.17         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.97/1.17      inference('demod', [status(thm)], ['7', '8'])).
% 0.97/1.17  thf('103', plain,
% 0.97/1.17      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.97/1.17          | (v1_xboole_0 @ X21)
% 0.97/1.17          | ~ (l1_struct_0 @ X22)
% 0.97/1.17          | (v2_struct_0 @ X22)
% 0.97/1.17          | (v1_xboole_0 @ X23)
% 0.97/1.17          | ~ (v2_waybel_0 @ X23 @ (k3_yellow_1 @ X21))
% 0.97/1.17          | ~ (v13_waybel_0 @ X23 @ (k3_yellow_1 @ X21))
% 0.97/1.17          | ~ (m1_subset_1 @ X23 @ 
% 0.97/1.17               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X21))))
% 0.97/1.17          | ~ (v2_struct_0 @ (k3_yellow19 @ X22 @ X21 @ X23)))),
% 0.97/1.17      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.97/1.17  thf('104', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('105', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('106', plain,
% 0.97/1.17      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.97/1.17  thf('107', plain,
% 0.97/1.17      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.97/1.17          | (v1_xboole_0 @ X21)
% 0.97/1.17          | ~ (l1_struct_0 @ X22)
% 0.97/1.17          | (v2_struct_0 @ X22)
% 0.97/1.17          | (v1_xboole_0 @ X23)
% 0.97/1.17          | ~ (v2_waybel_0 @ X23 @ (k3_lattice3 @ (k1_lattice3 @ X21)))
% 0.97/1.17          | ~ (v13_waybel_0 @ X23 @ (k3_lattice3 @ (k1_lattice3 @ X21)))
% 0.97/1.17          | ~ (m1_subset_1 @ X23 @ 
% 0.97/1.17               (k1_zfmisc_1 @ 
% 0.97/1.17                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X21)))))
% 0.97/1.17          | ~ (v2_struct_0 @ (k3_yellow19 @ X22 @ X21 @ X23)))),
% 0.97/1.17      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 0.97/1.17  thf('108', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.97/1.17               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.97/1.17          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.97/1.17               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.97/1.17          | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17          | (v2_struct_0 @ X0)
% 0.97/1.17          | ~ (l1_struct_0 @ X0)
% 0.97/1.17          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.97/1.17               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.97/1.17      inference('sup-', [status(thm)], ['102', '107'])).
% 0.97/1.17  thf('109', plain,
% 0.97/1.17      ((v13_waybel_0 @ sk_B_1 @ 
% 0.97/1.17        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.97/1.17      inference('demod', [status(thm)], ['16', '17'])).
% 0.97/1.17  thf('110', plain,
% 0.97/1.17      ((v2_waybel_0 @ sk_B_1 @ 
% 0.97/1.17        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.97/1.17      inference('demod', [status(thm)], ['19', '20'])).
% 0.97/1.17  thf('111', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17          | (v2_struct_0 @ X0)
% 0.97/1.17          | ~ (l1_struct_0 @ X0)
% 0.97/1.17          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.97/1.17               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.97/1.17      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.97/1.17  thf('112', plain,
% 0.97/1.17      ((~ (l1_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17        | ~ (l1_struct_0 @ sk_A)
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['101', '111'])).
% 0.97/1.17  thf('113', plain,
% 0.97/1.17      ((~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17        | ~ (l1_struct_0 @ sk_A))),
% 0.97/1.17      inference('simplify', [status(thm)], ['112'])).
% 0.97/1.17  thf('114', plain,
% 0.97/1.17      ((((v1_xboole_0 @ sk_B_1)
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)
% 0.97/1.17         | ~ (l1_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ sk_B_1)))
% 0.97/1.17         <= (((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('sup-', [status(thm)], ['100', '113'])).
% 0.97/1.17  thf('115', plain,
% 0.97/1.17      (((~ (l1_struct_0 @ sk_A)
% 0.97/1.17         | (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ sk_B_1)))
% 0.97/1.17         <= (((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('simplify', [status(thm)], ['114'])).
% 0.97/1.17  thf('116', plain,
% 0.97/1.17      (((~ (l1_pre_topc @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)))
% 0.97/1.17         <= (((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('sup-', [status(thm)], ['4', '115'])).
% 0.97/1.17  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('118', plain,
% 0.97/1.17      ((((v1_xboole_0 @ sk_B_1)
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)))
% 0.97/1.17         <= (((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('demod', [status(thm)], ['116', '117'])).
% 0.97/1.17  thf('119', plain,
% 0.97/1.17      ((~ (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.97/1.17         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.97/1.17      inference('split', [status(esa)], ['0'])).
% 0.97/1.17  thf('120', plain,
% 0.97/1.17      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ sk_B_1)))
% 0.97/1.17         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)) & 
% 0.97/1.17             ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('sup-', [status(thm)], ['118', '119'])).
% 0.97/1.17  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('122', plain,
% 0.97/1.17      ((((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.97/1.17         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)) & 
% 0.97/1.17             ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('clc', [status(thm)], ['120', '121'])).
% 0.97/1.17  thf('123', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('124', plain,
% 0.97/1.17      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.97/1.17         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)) & 
% 0.97/1.17             ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('clc', [status(thm)], ['122', '123'])).
% 0.97/1.17  thf('125', plain,
% 0.97/1.17      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.97/1.17         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)) & 
% 0.97/1.17             ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('sup+', [status(thm)], ['3', '124'])).
% 0.97/1.17  thf('126', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf(t30_connsp_2, axiom,
% 0.97/1.17    (![A:$i]:
% 0.97/1.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.97/1.17       ( ![B:$i]:
% 0.97/1.17         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.97/1.17           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.97/1.17  thf('127', plain,
% 0.97/1.17      (![X18 : $i, X19 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.97/1.17          | (r2_hidden @ X18 @ (k1_connsp_2 @ X19 @ X18))
% 0.97/1.17          | ~ (l1_pre_topc @ X19)
% 0.97/1.17          | ~ (v2_pre_topc @ X19)
% 0.97/1.17          | (v2_struct_0 @ X19))),
% 0.97/1.17      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.97/1.17  thf('128', plain,
% 0.97/1.17      (((v2_struct_0 @ sk_A)
% 0.97/1.17        | ~ (v2_pre_topc @ sk_A)
% 0.97/1.17        | ~ (l1_pre_topc @ sk_A)
% 0.97/1.17        | (r2_hidden @ sk_C_1 @ (k1_connsp_2 @ sk_A @ sk_C_1)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['126', '127'])).
% 0.97/1.17  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('131', plain,
% 0.97/1.17      (((v2_struct_0 @ sk_A)
% 0.97/1.17        | (r2_hidden @ sk_C_1 @ (k1_connsp_2 @ sk_A @ sk_C_1)))),
% 0.97/1.17      inference('demod', [status(thm)], ['128', '129', '130'])).
% 0.97/1.17  thf('132', plain, (~ (v2_struct_0 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('133', plain, ((r2_hidden @ sk_C_1 @ (k1_connsp_2 @ sk_A @ sk_C_1))),
% 0.97/1.17      inference('clc', [status(thm)], ['131', '132'])).
% 0.97/1.17  thf('134', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf(dt_k1_connsp_2, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.97/1.17         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.97/1.17       ( m1_subset_1 @
% 0.97/1.17         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.97/1.17  thf('135', plain,
% 0.97/1.17      (![X16 : $i, X17 : $i]:
% 0.97/1.17         (~ (l1_pre_topc @ X16)
% 0.97/1.17          | ~ (v2_pre_topc @ X16)
% 0.97/1.17          | (v2_struct_0 @ X16)
% 0.97/1.17          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.97/1.17          | (m1_subset_1 @ (k1_connsp_2 @ X16 @ X17) @ 
% 0.97/1.17             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 0.97/1.17      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.97/1.17  thf('136', plain,
% 0.97/1.17      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_C_1) @ 
% 0.97/1.17         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | ~ (v2_pre_topc @ sk_A)
% 0.97/1.17        | ~ (l1_pre_topc @ sk_A))),
% 0.97/1.17      inference('sup-', [status(thm)], ['134', '135'])).
% 0.97/1.17  thf('137', plain, ((v2_pre_topc @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('139', plain,
% 0.97/1.17      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_C_1) @ 
% 0.97/1.17         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.97/1.17        | (v2_struct_0 @ sk_A))),
% 0.97/1.17      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.97/1.17  thf('140', plain, (~ (v2_struct_0 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('141', plain,
% 0.97/1.17      ((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_C_1) @ 
% 0.97/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('clc', [status(thm)], ['139', '140'])).
% 0.97/1.17  thf(t3_subset, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.97/1.17  thf('142', plain,
% 0.97/1.17      (![X10 : $i, X11 : $i]:
% 0.97/1.17         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t3_subset])).
% 0.97/1.17  thf('143', plain,
% 0.97/1.17      ((r1_tarski @ (k1_connsp_2 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.97/1.17      inference('sup-', [status(thm)], ['141', '142'])).
% 0.97/1.17  thf(d3_tarski, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( r1_tarski @ A @ B ) <=>
% 0.97/1.17       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.97/1.17  thf('144', plain,
% 0.97/1.17      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.97/1.17         (~ (r2_hidden @ X3 @ X4)
% 0.97/1.17          | (r2_hidden @ X3 @ X5)
% 0.97/1.17          | ~ (r1_tarski @ X4 @ X5))),
% 0.97/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.17  thf('145', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.97/1.17          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_A @ sk_C_1)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['143', '144'])).
% 0.97/1.17  thf('146', plain, ((r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.97/1.17      inference('sup-', [status(thm)], ['133', '145'])).
% 0.97/1.17  thf(d1_xboole_0, axiom,
% 0.97/1.17    (![A:$i]:
% 0.97/1.17     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.97/1.17  thf('147', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.97/1.17      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.97/1.17  thf('148', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.97/1.17      inference('sup-', [status(thm)], ['146', '147'])).
% 0.97/1.17  thf('149', plain,
% 0.97/1.17      ((~ (l1_struct_0 @ sk_A))
% 0.97/1.17         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)) & 
% 0.97/1.17             ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('clc', [status(thm)], ['125', '148'])).
% 0.97/1.17  thf('150', plain,
% 0.97/1.17      ((~ (l1_pre_topc @ sk_A))
% 0.97/1.17         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)) & 
% 0.97/1.17             ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('sup-', [status(thm)], ['2', '149'])).
% 0.97/1.17  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('152', plain,
% 0.97/1.17      (((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)) | 
% 0.97/1.17       ~
% 0.97/1.17       ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17         (k10_yellow_6 @ sk_A @ 
% 0.97/1.17          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.97/1.17      inference('demod', [status(thm)], ['150', '151'])).
% 0.97/1.17  thf('153', plain,
% 0.97/1.17      (((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)) | 
% 0.97/1.17       ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17         (k10_yellow_6 @ sk_A @ 
% 0.97/1.17          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.97/1.17      inference('split', [status(esa)], ['66'])).
% 0.97/1.17  thf('154', plain,
% 0.97/1.17      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.97/1.17      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.97/1.17  thf('155', plain,
% 0.97/1.17      (![X13 : $i]:
% 0.97/1.17         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.97/1.17      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.97/1.17  thf('156', plain,
% 0.97/1.17      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.97/1.17      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.97/1.17  thf('157', plain,
% 0.97/1.17      (((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.97/1.17         <= (((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.97/1.17      inference('split', [status(esa)], ['66'])).
% 0.97/1.17  thf('158', plain,
% 0.97/1.17      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.97/1.17      inference('demod', [status(thm)], ['25', '26'])).
% 0.97/1.17  thf('159', plain,
% 0.97/1.17      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.97/1.17      inference('demod', [status(thm)], ['46', '47'])).
% 0.97/1.17  thf('160', plain,
% 0.97/1.17      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | (l1_waybel_0 @ 
% 0.97/1.17           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.97/1.17      inference('demod', [status(thm)], ['63', '64'])).
% 0.97/1.17  thf('161', plain,
% 0.97/1.17      (((sk_B_1)
% 0.97/1.17         = (k2_yellow19 @ sk_A @ 
% 0.97/1.17            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.97/1.17      inference('clc', [status(thm)], ['91', '92'])).
% 0.97/1.17  thf('162', plain,
% 0.97/1.17      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.97/1.17         ((v2_struct_0 @ X30)
% 0.97/1.17          | ~ (v4_orders_2 @ X30)
% 0.97/1.17          | ~ (v7_waybel_0 @ X30)
% 0.97/1.17          | ~ (l1_waybel_0 @ X30 @ X31)
% 0.97/1.17          | ~ (r2_waybel_7 @ X31 @ (k2_yellow19 @ X31 @ X30) @ X32)
% 0.97/1.17          | (r2_hidden @ X32 @ (k10_yellow_6 @ X31 @ X30))
% 0.97/1.17          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 0.97/1.17          | ~ (l1_pre_topc @ X31)
% 0.97/1.17          | ~ (v2_pre_topc @ X31)
% 0.97/1.17          | (v2_struct_0 @ X31))),
% 0.97/1.17      inference('cnf', [status(esa)], [t13_yellow19])).
% 0.97/1.17  thf('163', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         (~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.97/1.17          | (v2_struct_0 @ sk_A)
% 0.97/1.17          | ~ (v2_pre_topc @ sk_A)
% 0.97/1.17          | ~ (l1_pre_topc @ sk_A)
% 0.97/1.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.97/1.17          | (r2_hidden @ X0 @ 
% 0.97/1.17             (k10_yellow_6 @ sk_A @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.97/1.17          | ~ (l1_waybel_0 @ 
% 0.97/1.17               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.97/1.17          | ~ (v7_waybel_0 @ 
% 0.97/1.17               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | ~ (v4_orders_2 @ 
% 0.97/1.17               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['161', '162'])).
% 0.97/1.17  thf('164', plain, ((v2_pre_topc @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('165', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('166', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         (~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.97/1.17          | (v2_struct_0 @ sk_A)
% 0.97/1.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.97/1.17          | (r2_hidden @ X0 @ 
% 0.97/1.17             (k10_yellow_6 @ sk_A @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.97/1.17          | ~ (l1_waybel_0 @ 
% 0.97/1.17               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.97/1.17          | ~ (v7_waybel_0 @ 
% 0.97/1.17               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | ~ (v4_orders_2 @ 
% 0.97/1.17               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.97/1.17      inference('demod', [status(thm)], ['163', '164', '165'])).
% 0.97/1.17  thf('167', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((v1_xboole_0 @ sk_B_1)
% 0.97/1.17          | (v2_struct_0 @ sk_A)
% 0.97/1.17          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | ~ (v4_orders_2 @ 
% 0.97/1.17               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | ~ (v7_waybel_0 @ 
% 0.97/1.17               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | (r2_hidden @ X0 @ 
% 0.97/1.17             (k10_yellow_6 @ sk_A @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.97/1.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.97/1.17          | (v2_struct_0 @ sk_A)
% 0.97/1.17          | ~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0))),
% 0.97/1.17      inference('sup-', [status(thm)], ['160', '166'])).
% 0.97/1.17  thf('168', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         (~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.97/1.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.97/1.17          | (r2_hidden @ X0 @ 
% 0.97/1.17             (k10_yellow_6 @ sk_A @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.97/1.17          | ~ (v7_waybel_0 @ 
% 0.97/1.17               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | ~ (v4_orders_2 @ 
% 0.97/1.17               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17          | (v2_struct_0 @ sk_A)
% 0.97/1.17          | (v1_xboole_0 @ sk_B_1))),
% 0.97/1.17      inference('simplify', [status(thm)], ['167'])).
% 0.97/1.17  thf('169', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((v1_xboole_0 @ sk_B_1)
% 0.97/1.17          | (v2_struct_0 @ sk_A)
% 0.97/1.17          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17          | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17          | (v2_struct_0 @ sk_A)
% 0.97/1.17          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | ~ (v4_orders_2 @ 
% 0.97/1.17               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | (r2_hidden @ X0 @ 
% 0.97/1.17             (k10_yellow_6 @ sk_A @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.97/1.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.97/1.17          | ~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0))),
% 0.97/1.17      inference('sup-', [status(thm)], ['159', '168'])).
% 0.97/1.17  thf('170', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         (~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.97/1.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.97/1.17          | (r2_hidden @ X0 @ 
% 0.97/1.17             (k10_yellow_6 @ sk_A @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.97/1.17          | ~ (v4_orders_2 @ 
% 0.97/1.17               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17          | (v2_struct_0 @ sk_A)
% 0.97/1.17          | (v1_xboole_0 @ sk_B_1))),
% 0.97/1.17      inference('simplify', [status(thm)], ['169'])).
% 0.97/1.17  thf('171', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((v1_xboole_0 @ sk_B_1)
% 0.97/1.17          | (v2_struct_0 @ sk_A)
% 0.97/1.17          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17          | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17          | (v2_struct_0 @ sk_A)
% 0.97/1.17          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | (r2_hidden @ X0 @ 
% 0.97/1.17             (k10_yellow_6 @ sk_A @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.97/1.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.97/1.17          | ~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0))),
% 0.97/1.17      inference('sup-', [status(thm)], ['158', '170'])).
% 0.97/1.17  thf('172', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         (~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.97/1.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.97/1.17          | (r2_hidden @ X0 @ 
% 0.97/1.17             (k10_yellow_6 @ sk_A @ 
% 0.97/1.17              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.97/1.17          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17          | (v2_struct_0 @ sk_A)
% 0.97/1.17          | (v1_xboole_0 @ sk_B_1))),
% 0.97/1.17      inference('simplify', [status(thm)], ['171'])).
% 0.97/1.17  thf('173', plain,
% 0.97/1.17      ((((v1_xboole_0 @ sk_B_1)
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | (r2_hidden @ sk_C_1 @ 
% 0.97/1.17            (k10_yellow_6 @ sk_A @ 
% 0.97/1.17             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.97/1.17         | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))))
% 0.97/1.17         <= (((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['157', '172'])).
% 0.97/1.17  thf('174', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('175', plain,
% 0.97/1.17      ((((v1_xboole_0 @ sk_B_1)
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | (r2_hidden @ sk_C_1 @ 
% 0.97/1.17            (k10_yellow_6 @ sk_A @ 
% 0.97/1.17             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))
% 0.97/1.17         <= (((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.97/1.17      inference('demod', [status(thm)], ['173', '174'])).
% 0.97/1.17  thf('176', plain,
% 0.97/1.17      ((~ (r2_hidden @ sk_C_1 @ 
% 0.97/1.17           (k10_yellow_6 @ sk_A @ 
% 0.97/1.17            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 0.97/1.17         <= (~
% 0.97/1.17             ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.97/1.17      inference('split', [status(esa)], ['0'])).
% 0.97/1.17  thf('177', plain,
% 0.97/1.17      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ sk_B_1)))
% 0.97/1.17         <= (~
% 0.97/1.17             ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.97/1.17             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['175', '176'])).
% 0.97/1.17  thf('178', plain,
% 0.97/1.17      ((~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.97/1.17        | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17        | ~ (l1_struct_0 @ sk_A))),
% 0.97/1.17      inference('simplify', [status(thm)], ['112'])).
% 0.97/1.17  thf('179', plain,
% 0.97/1.17      ((((v1_xboole_0 @ sk_B_1)
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | ~ (l1_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ sk_B_1)))
% 0.97/1.17         <= (~
% 0.97/1.17             ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.97/1.17             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['177', '178'])).
% 0.97/1.17  thf('180', plain,
% 0.97/1.17      (((~ (l1_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ sk_B_1)))
% 0.97/1.17         <= (~
% 0.97/1.17             ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.97/1.17             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.97/1.17      inference('simplify', [status(thm)], ['179'])).
% 0.97/1.17  thf('181', plain,
% 0.97/1.17      (((~ (l1_pre_topc @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ sk_B_1)
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.97/1.17         <= (~
% 0.97/1.17             ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.97/1.17             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['156', '180'])).
% 0.97/1.17  thf('182', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('183', plain,
% 0.97/1.17      ((((v1_xboole_0 @ sk_B_1)
% 0.97/1.17         | (v2_struct_0 @ sk_A)
% 0.97/1.17         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.97/1.17         <= (~
% 0.97/1.17             ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.97/1.17             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.97/1.17      inference('demod', [status(thm)], ['181', '182'])).
% 0.97/1.17  thf('184', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('185', plain,
% 0.97/1.17      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.97/1.17         <= (~
% 0.97/1.17             ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.97/1.17             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.97/1.17      inference('clc', [status(thm)], ['183', '184'])).
% 0.97/1.17  thf('186', plain, (~ (v2_struct_0 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('187', plain,
% 0.97/1.17      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.97/1.17         <= (~
% 0.97/1.17             ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.97/1.17             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.97/1.17      inference('clc', [status(thm)], ['185', '186'])).
% 0.97/1.17  thf('188', plain,
% 0.97/1.17      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.97/1.17         <= (~
% 0.97/1.17             ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.97/1.17             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['155', '187'])).
% 0.97/1.17  thf('189', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.97/1.17      inference('sup-', [status(thm)], ['146', '147'])).
% 0.97/1.17  thf('190', plain,
% 0.97/1.17      ((~ (l1_struct_0 @ sk_A))
% 0.97/1.17         <= (~
% 0.97/1.17             ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.97/1.17             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.97/1.17      inference('clc', [status(thm)], ['188', '189'])).
% 0.97/1.17  thf('191', plain,
% 0.97/1.17      ((~ (l1_pre_topc @ sk_A))
% 0.97/1.17         <= (~
% 0.97/1.17             ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17               (k10_yellow_6 @ sk_A @ 
% 0.97/1.17                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.97/1.17             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['154', '190'])).
% 0.97/1.17  thf('192', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('193', plain,
% 0.97/1.17      (~ ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C_1)) | 
% 0.97/1.17       ((r2_hidden @ sk_C_1 @ 
% 0.97/1.17         (k10_yellow_6 @ sk_A @ 
% 0.97/1.17          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.97/1.17      inference('demod', [status(thm)], ['191', '192'])).
% 0.97/1.17  thf('194', plain, ($false),
% 0.97/1.17      inference('sat_resolution*', [status(thm)], ['1', '152', '153', '193'])).
% 0.97/1.17  
% 0.97/1.17  % SZS output end Refutation
% 0.97/1.17  
% 0.97/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
