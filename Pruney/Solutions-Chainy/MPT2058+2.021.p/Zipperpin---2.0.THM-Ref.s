%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VpwDpkNkad

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:52 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  212 ( 584 expanded)
%              Number of leaves         :   37 ( 197 expanded)
%              Depth                    :   31
%              Number of atoms          : 2939 (11551 expanded)
%              Number of equality atoms :   32 ( 154 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('2',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('7',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ X10 ) ) )
      | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ X10 ) )
      | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X10 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('10',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('11',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('12',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('13',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) )
      | ~ ( v2_waybel_0 @ X12 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) )
      | ~ ( v13_waybel_0 @ X12 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X11 @ X10 @ X12 ) ) ) ),
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
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('18',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('21',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
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
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v2_waybel_0 @ X9 @ ( k3_yellow_1 @ X7 ) )
      | ~ ( v13_waybel_0 @ X9 @ ( k3_yellow_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X7 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X8 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('35',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('36',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('37',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v2_waybel_0 @ X9 @ ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) )
      | ~ ( v13_waybel_0 @ X9 @ ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X8 @ X7 @ X9 ) ) ) ),
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
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v2_waybel_0 @ X6 @ ( k3_yellow_1 @ X4 ) )
      | ~ ( v13_waybel_0 @ X6 @ ( k3_yellow_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X4 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X5 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('52',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('53',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('54',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('55',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v2_waybel_0 @ X6 @ ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) )
      | ~ ( v13_waybel_0 @ X6 @ ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X5 @ X4 @ X6 ) @ X5 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v7_waybel_0 @ X13 )
      | ~ ( l1_waybel_0 @ X13 @ X14 )
      | ~ ( r3_waybel_9 @ X14 @ X13 @ X15 )
      | ( r1_waybel_7 @ X14 @ ( k2_yellow19 @ X14 @ X13 ) @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
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

thf('75',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('76',plain,(
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

thf('77',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( v1_subset_1 @ X16 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X17 ) ) ) )
      | ~ ( v2_waybel_0 @ X16 @ ( k3_yellow_1 @ ( k2_struct_0 @ X17 ) ) )
      | ~ ( v13_waybel_0 @ X16 @ ( k3_yellow_1 @ ( k2_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X17 ) ) ) ) )
      | ( X16
        = ( k2_yellow19 @ X17 @ ( k3_yellow19 @ X17 @ ( k2_struct_0 @ X17 ) @ X16 ) ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('78',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('79',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('80',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('81',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('82',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( v1_subset_1 @ X16 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X17 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X16 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X17 ) ) ) )
      | ~ ( v13_waybel_0 @ X16 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X17 ) ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X17 ) ) ) ) ) )
      | ( X16
        = ( k2_yellow19 @ X17 @ ( k3_yellow19 @ X17 @ ( k2_struct_0 @ X17 ) @ X16 ) ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['76','82'])).

thf('84',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('85',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('86',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['74','94'])).

thf('96',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['47','96'])).

thf('98',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['97'])).

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
    inference('sup-',[status(thm)],['30','98'])).

thf('100',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('103',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v2_waybel_0 @ X6 @ ( k3_yellow_1 @ X4 ) )
      | ~ ( v13_waybel_0 @ X6 @ ( k3_yellow_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X4 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X5 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('104',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('105',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('106',plain,(
    ! [X3: $i] :
      ( ( k3_yellow_1 @ X3 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('107',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v2_waybel_0 @ X6 @ ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) )
      | ~ ( v13_waybel_0 @ X6 @ ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X5 @ X4 @ X6 ) ) ) ),
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

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('125',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('126',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','128'])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['65'])).

thf('133',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('134',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('135',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['65'])).

thf('136',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('137',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('138',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('139',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('140',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v7_waybel_0 @ X13 )
      | ~ ( l1_waybel_0 @ X13 @ X14 )
      | ~ ( r1_waybel_7 @ X14 @ ( k2_yellow19 @ X14 @ X13 ) @ X15 )
      | ( r3_waybel_9 @ X14 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('141',plain,(
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
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,(
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
    inference('sup-',[status(thm)],['138','144'])).

thf('146',plain,(
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
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
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
    inference('sup-',[status(thm)],['137','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
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
    inference('sup-',[status(thm)],['136','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['135','150'])).

thf('152',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('155',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['112'])).

thf('157',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['134','158'])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('167',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['167','168'])).

thf('170',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['133','169'])).

thf('171',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','131','132','172'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VpwDpkNkad
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:19:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 77 iterations in 0.060s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.19/0.47  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.47  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.19/0.47  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 0.19/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.19/0.47  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.19/0.47  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.19/0.47  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.19/0.47  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.47  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.19/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.47  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.19/0.47  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.19/0.47  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.19/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.47  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.19/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.19/0.47  thf(t17_yellow19, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.47             ( v1_subset_1 @
% 0.19/0.47               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.19/0.47             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.47             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.47             ( m1_subset_1 @
% 0.19/0.47               B @ 
% 0.19/0.47               ( k1_zfmisc_1 @
% 0.19/0.47                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.19/0.47           ( ![C:$i]:
% 0.19/0.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.47               ( ( r3_waybel_9 @
% 0.19/0.47                   A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.19/0.47                 ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.47            ( l1_pre_topc @ A ) ) =>
% 0.19/0.47          ( ![B:$i]:
% 0.19/0.47            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.47                ( v1_subset_1 @
% 0.19/0.47                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.19/0.47                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.47                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.47                ( m1_subset_1 @
% 0.19/0.47                  B @ 
% 0.19/0.47                  ( k1_zfmisc_1 @
% 0.19/0.47                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.19/0.47              ( ![C:$i]:
% 0.19/0.47                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.47                  ( ( r3_waybel_9 @
% 0.19/0.47                      A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.19/0.47                    ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t17_yellow19])).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.19/0.47        | ~ (r3_waybel_9 @ sk_A @ 
% 0.19/0.47             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.19/0.47       ~
% 0.19/0.47       ((r3_waybel_9 @ sk_A @ 
% 0.19/0.47         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.19/0.47      inference('split', [status(esa)], ['0'])).
% 0.19/0.47  thf(dt_l1_pre_topc, axiom,
% 0.19/0.47    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.47  thf('2', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.47  thf('3', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.47  thf('4', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.47  thf(dt_k2_struct_0, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( l1_struct_0 @ A ) =>
% 0.19/0.47       ( m1_subset_1 @
% 0.19/0.47         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.19/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.47          | ~ (l1_struct_0 @ X0))),
% 0.19/0.47      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_B @ 
% 0.19/0.47        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(d2_yellow_1, axiom,
% 0.19/0.47    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.19/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.48  thf(fc5_yellow19, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.19/0.48         ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.19/0.48         ( ~( v1_xboole_0 @ C ) ) & 
% 0.19/0.48         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.19/0.48         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.19/0.48         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.19/0.48         ( m1_subset_1 @
% 0.19/0.48           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.19/0.48       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.19/0.48         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.19/0.48         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.19/0.48          | (v1_xboole_0 @ X10)
% 0.19/0.48          | ~ (l1_struct_0 @ X11)
% 0.19/0.48          | (v2_struct_0 @ X11)
% 0.19/0.48          | (v1_xboole_0 @ X12)
% 0.19/0.48          | ~ (v1_subset_1 @ X12 @ (u1_struct_0 @ (k3_yellow_1 @ X10)))
% 0.19/0.48          | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.19/0.48          | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.19/0.48          | ~ (m1_subset_1 @ X12 @ 
% 0.19/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X10))))
% 0.19/0.48          | (v7_waybel_0 @ (k3_yellow19 @ X11 @ X10 @ X12)))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.19/0.48          | (v1_xboole_0 @ X10)
% 0.19/0.48          | ~ (l1_struct_0 @ X11)
% 0.19/0.48          | (v2_struct_0 @ X11)
% 0.19/0.48          | (v1_xboole_0 @ X12)
% 0.19/0.48          | ~ (v1_subset_1 @ X12 @ 
% 0.19/0.48               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X10))))
% 0.19/0.48          | ~ (v2_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.19/0.48          | ~ (v13_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.19/0.48          | ~ (m1_subset_1 @ X12 @ 
% 0.19/0.48               (k1_zfmisc_1 @ 
% 0.19/0.48                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X10)))))
% 0.19/0.48          | (v7_waybel_0 @ (k3_yellow19 @ X11 @ X10 @ X12)))),
% 0.19/0.48      inference('demod', [status(thm)], ['9', '10', '11', '12', '13'])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | ~ (v13_waybel_0 @ sk_B @ 
% 0.19/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.19/0.48          | ~ (v2_waybel_0 @ sk_B @ 
% 0.19/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.19/0.48          | ~ (v1_subset_1 @ sk_B @ 
% 0.19/0.48               (u1_struct_0 @ 
% 0.19/0.48                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.19/0.48          | (v1_xboole_0 @ sk_B)
% 0.19/0.48          | (v2_struct_0 @ X0)
% 0.19/0.48          | ~ (l1_struct_0 @ X0)
% 0.19/0.48          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.19/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['8', '14'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      ((v13_waybel_0 @ sk_B @ 
% 0.19/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      ((v2_waybel_0 @ sk_B @ 
% 0.19/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      ((v1_subset_1 @ sk_B @ 
% 0.19/0.48        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      ((v1_subset_1 @ sk_B @ 
% 0.19/0.48        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.19/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | (v1_xboole_0 @ sk_B)
% 0.19/0.48          | (v2_struct_0 @ X0)
% 0.19/0.48          | ~ (l1_struct_0 @ X0)
% 0.19/0.48          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.19/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['15', '18', '21', '24'])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      ((~ (l1_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A)
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['5', '25'])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.48      inference('simplify', [status(thm)], ['26'])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['4', '27'])).
% 0.19/0.48  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.48      inference('demod', [status(thm)], ['28', '29'])).
% 0.19/0.48  thf('31', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.19/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.48          | ~ (l1_struct_0 @ X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.19/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.48  thf(fc4_yellow19, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.19/0.48         ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.19/0.48         ( ~( v1_xboole_0 @ C ) ) & 
% 0.19/0.48         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.19/0.48         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.19/0.48         ( m1_subset_1 @
% 0.19/0.48           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.19/0.48       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.19/0.48         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.19/0.48         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.19/0.48         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.19/0.48          | (v1_xboole_0 @ X7)
% 0.19/0.48          | ~ (l1_struct_0 @ X8)
% 0.19/0.48          | (v2_struct_0 @ X8)
% 0.19/0.48          | (v1_xboole_0 @ X9)
% 0.19/0.48          | ~ (v2_waybel_0 @ X9 @ (k3_yellow_1 @ X7))
% 0.19/0.48          | ~ (v13_waybel_0 @ X9 @ (k3_yellow_1 @ X7))
% 0.19/0.48          | ~ (m1_subset_1 @ X9 @ 
% 0.19/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X7))))
% 0.19/0.48          | (v4_orders_2 @ (k3_yellow19 @ X8 @ X7 @ X9)))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('37', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('38', plain,
% 0.19/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.19/0.48          | (v1_xboole_0 @ X7)
% 0.19/0.48          | ~ (l1_struct_0 @ X8)
% 0.19/0.48          | (v2_struct_0 @ X8)
% 0.19/0.48          | (v1_xboole_0 @ X9)
% 0.19/0.48          | ~ (v2_waybel_0 @ X9 @ (k3_lattice3 @ (k1_lattice3 @ X7)))
% 0.19/0.48          | ~ (v13_waybel_0 @ X9 @ (k3_lattice3 @ (k1_lattice3 @ X7)))
% 0.19/0.48          | ~ (m1_subset_1 @ X9 @ 
% 0.19/0.48               (k1_zfmisc_1 @ 
% 0.19/0.48                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X7)))))
% 0.19/0.48          | (v4_orders_2 @ (k3_yellow19 @ X8 @ X7 @ X9)))),
% 0.19/0.48      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.19/0.48  thf('39', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | ~ (v13_waybel_0 @ sk_B @ 
% 0.19/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.19/0.48          | ~ (v2_waybel_0 @ sk_B @ 
% 0.19/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.19/0.48          | (v1_xboole_0 @ sk_B)
% 0.19/0.48          | (v2_struct_0 @ X0)
% 0.19/0.48          | ~ (l1_struct_0 @ X0)
% 0.19/0.48          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.19/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['33', '38'])).
% 0.19/0.48  thf('40', plain,
% 0.19/0.48      ((v13_waybel_0 @ sk_B @ 
% 0.19/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.48  thf('41', plain,
% 0.19/0.48      ((v2_waybel_0 @ sk_B @ 
% 0.19/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.48  thf('42', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | (v1_xboole_0 @ sk_B)
% 0.19/0.48          | (v2_struct_0 @ X0)
% 0.19/0.48          | ~ (l1_struct_0 @ X0)
% 0.19/0.48          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.19/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.19/0.48  thf('43', plain,
% 0.19/0.48      ((~ (l1_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A)
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['32', '42'])).
% 0.19/0.48  thf('44', plain,
% 0.19/0.48      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.48      inference('simplify', [status(thm)], ['43'])).
% 0.19/0.48  thf('45', plain,
% 0.19/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['31', '44'])).
% 0.19/0.48  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('47', plain,
% 0.19/0.48      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.48      inference('demod', [status(thm)], ['45', '46'])).
% 0.19/0.48  thf('48', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.48  thf('49', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.19/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.48          | ~ (l1_struct_0 @ X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.19/0.48  thf('50', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.19/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.48  thf(dt_k3_yellow19, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.19/0.48         ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.19/0.48         ( ~( v1_xboole_0 @ C ) ) & 
% 0.19/0.48         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.19/0.48         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.19/0.48         ( m1_subset_1 @
% 0.19/0.48           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.19/0.48       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.19/0.48         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.19/0.48         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.19/0.48  thf('51', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.19/0.48          | (v1_xboole_0 @ X4)
% 0.19/0.48          | ~ (l1_struct_0 @ X5)
% 0.19/0.48          | (v2_struct_0 @ X5)
% 0.19/0.48          | (v1_xboole_0 @ X6)
% 0.19/0.48          | ~ (v2_waybel_0 @ X6 @ (k3_yellow_1 @ X4))
% 0.19/0.48          | ~ (v13_waybel_0 @ X6 @ (k3_yellow_1 @ X4))
% 0.19/0.48          | ~ (m1_subset_1 @ X6 @ 
% 0.19/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X4))))
% 0.19/0.48          | (l1_waybel_0 @ (k3_yellow19 @ X5 @ X4 @ X6) @ X5))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.19/0.48  thf('52', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('53', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('54', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('55', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.19/0.48          | (v1_xboole_0 @ X4)
% 0.19/0.48          | ~ (l1_struct_0 @ X5)
% 0.19/0.48          | (v2_struct_0 @ X5)
% 0.19/0.48          | (v1_xboole_0 @ X6)
% 0.19/0.48          | ~ (v2_waybel_0 @ X6 @ (k3_lattice3 @ (k1_lattice3 @ X4)))
% 0.19/0.48          | ~ (v13_waybel_0 @ X6 @ (k3_lattice3 @ (k1_lattice3 @ X4)))
% 0.19/0.48          | ~ (m1_subset_1 @ X6 @ 
% 0.19/0.48               (k1_zfmisc_1 @ 
% 0.19/0.48                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X4)))))
% 0.19/0.48          | (l1_waybel_0 @ (k3_yellow19 @ X5 @ X4 @ X6) @ X5))),
% 0.19/0.48      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.19/0.48  thf('56', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.19/0.48          | ~ (v13_waybel_0 @ sk_B @ 
% 0.19/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.19/0.48          | ~ (v2_waybel_0 @ sk_B @ 
% 0.19/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.19/0.48          | (v1_xboole_0 @ sk_B)
% 0.19/0.48          | (v2_struct_0 @ X0)
% 0.19/0.48          | ~ (l1_struct_0 @ X0)
% 0.19/0.48          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.19/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['50', '55'])).
% 0.19/0.48  thf('57', plain,
% 0.19/0.48      ((v13_waybel_0 @ sk_B @ 
% 0.19/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.48  thf('58', plain,
% 0.19/0.48      ((v2_waybel_0 @ sk_B @ 
% 0.19/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.48  thf('59', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.19/0.48          | (v1_xboole_0 @ sk_B)
% 0.19/0.48          | (v2_struct_0 @ X0)
% 0.19/0.48          | ~ (l1_struct_0 @ X0)
% 0.19/0.48          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.19/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.19/0.48  thf('60', plain,
% 0.19/0.48      ((~ (l1_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A)
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.48           sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['49', '59'])).
% 0.19/0.48  thf('61', plain,
% 0.19/0.48      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.48         sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.48      inference('simplify', [status(thm)], ['60'])).
% 0.19/0.48  thf('62', plain,
% 0.19/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.48           sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['48', '61'])).
% 0.19/0.48  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('64', plain,
% 0.19/0.48      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.48           sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['62', '63'])).
% 0.19/0.48  thf('65', plain,
% 0.19/0.48      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.19/0.48        | (r3_waybel_9 @ sk_A @ 
% 0.19/0.48           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('66', plain,
% 0.19/0.48      (((r3_waybel_9 @ sk_A @ 
% 0.19/0.48         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.19/0.48         <= (((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('split', [status(esa)], ['65'])).
% 0.19/0.48  thf('67', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t12_yellow19, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.19/0.48             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.48               ( ( r3_waybel_9 @ A @ B @ C ) <=>
% 0.19/0.48                 ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.19/0.48  thf('68', plain,
% 0.19/0.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.48         ((v2_struct_0 @ X13)
% 0.19/0.48          | ~ (v4_orders_2 @ X13)
% 0.19/0.48          | ~ (v7_waybel_0 @ X13)
% 0.19/0.48          | ~ (l1_waybel_0 @ X13 @ X14)
% 0.19/0.48          | ~ (r3_waybel_9 @ X14 @ X13 @ X15)
% 0.19/0.48          | (r1_waybel_7 @ X14 @ (k2_yellow19 @ X14 @ X13) @ X15)
% 0.19/0.48          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.19/0.48          | ~ (l1_pre_topc @ X14)
% 0.19/0.48          | ~ (v2_pre_topc @ X14)
% 0.19/0.48          | (v2_struct_0 @ X14))),
% 0.19/0.48      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.19/0.48  thf('69', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v2_struct_0 @ sk_A)
% 0.19/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.48          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.19/0.48          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.19/0.48          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.19/0.48          | ~ (v7_waybel_0 @ X0)
% 0.19/0.48          | ~ (v4_orders_2 @ X0)
% 0.19/0.48          | (v2_struct_0 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['67', '68'])).
% 0.19/0.48  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('72', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v2_struct_0 @ sk_A)
% 0.19/0.48          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.19/0.48          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.19/0.48          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.19/0.48          | ~ (v7_waybel_0 @ X0)
% 0.19/0.48          | ~ (v4_orders_2 @ X0)
% 0.19/0.48          | (v2_struct_0 @ X0))),
% 0.19/0.48      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.19/0.48  thf('73', plain,
% 0.19/0.48      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48         | ~ (l1_waybel_0 @ 
% 0.19/0.48              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.19/0.48         | (r1_waybel_7 @ sk_A @ 
% 0.19/0.48            (k2_yellow19 @ sk_A @ 
% 0.19/0.48             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.19/0.48            sk_C)
% 0.19/0.48         | (v2_struct_0 @ sk_A)))
% 0.19/0.48         <= (((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['66', '72'])).
% 0.19/0.48  thf('74', plain,
% 0.19/0.48      ((((v1_xboole_0 @ sk_B)
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (r1_waybel_7 @ sk_A @ 
% 0.19/0.48            (k2_yellow19 @ sk_A @ 
% 0.19/0.48             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.19/0.48            sk_C)
% 0.19/0.48         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.19/0.48         <= (((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['64', '73'])).
% 0.19/0.48  thf('75', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.48  thf('76', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.19/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.48  thf(t15_yellow19, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.48             ( v1_subset_1 @
% 0.19/0.48               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.19/0.48             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.48             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.19/0.48             ( m1_subset_1 @
% 0.19/0.48               B @ 
% 0.19/0.48               ( k1_zfmisc_1 @
% 0.19/0.48                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.19/0.48           ( ( B ) =
% 0.19/0.48             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.19/0.48  thf('77', plain,
% 0.19/0.48      (![X16 : $i, X17 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ X16)
% 0.19/0.48          | ~ (v1_subset_1 @ X16 @ 
% 0.19/0.48               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X17))))
% 0.19/0.48          | ~ (v2_waybel_0 @ X16 @ (k3_yellow_1 @ (k2_struct_0 @ X17)))
% 0.19/0.48          | ~ (v13_waybel_0 @ X16 @ (k3_yellow_1 @ (k2_struct_0 @ X17)))
% 0.19/0.48          | ~ (m1_subset_1 @ X16 @ 
% 0.19/0.48               (k1_zfmisc_1 @ 
% 0.19/0.48                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X17)))))
% 0.19/0.48          | ((X16)
% 0.19/0.48              = (k2_yellow19 @ X17 @ 
% 0.19/0.48                 (k3_yellow19 @ X17 @ (k2_struct_0 @ X17) @ X16)))
% 0.19/0.48          | ~ (l1_struct_0 @ X17)
% 0.19/0.48          | (v2_struct_0 @ X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.19/0.48  thf('78', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('79', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('80', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('81', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('82', plain,
% 0.19/0.48      (![X16 : $i, X17 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ X16)
% 0.19/0.48          | ~ (v1_subset_1 @ X16 @ 
% 0.19/0.48               (u1_struct_0 @ 
% 0.19/0.48                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X17)))))
% 0.19/0.48          | ~ (v2_waybel_0 @ X16 @ 
% 0.19/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X17))))
% 0.19/0.48          | ~ (v13_waybel_0 @ X16 @ 
% 0.19/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X17))))
% 0.19/0.48          | ~ (m1_subset_1 @ X16 @ 
% 0.19/0.48               (k1_zfmisc_1 @ 
% 0.19/0.48                (u1_struct_0 @ 
% 0.19/0.48                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X17))))))
% 0.19/0.48          | ((X16)
% 0.19/0.48              = (k2_yellow19 @ X17 @ 
% 0.19/0.48                 (k3_yellow19 @ X17 @ (k2_struct_0 @ X17) @ X16)))
% 0.19/0.48          | ~ (l1_struct_0 @ X17)
% 0.19/0.48          | (v2_struct_0 @ X17))),
% 0.19/0.48      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 0.19/0.48  thf('83', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A)
% 0.19/0.48        | ((sk_B)
% 0.19/0.48            = (k2_yellow19 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.48        | ~ (v13_waybel_0 @ sk_B @ 
% 0.19/0.48             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.19/0.48        | ~ (v2_waybel_0 @ sk_B @ 
% 0.19/0.48             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.19/0.48        | ~ (v1_subset_1 @ sk_B @ 
% 0.19/0.48             (u1_struct_0 @ 
% 0.19/0.48              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.19/0.48        | (v1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['76', '82'])).
% 0.19/0.48  thf('84', plain,
% 0.19/0.48      ((v13_waybel_0 @ sk_B @ 
% 0.19/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.48  thf('85', plain,
% 0.19/0.48      ((v2_waybel_0 @ sk_B @ 
% 0.19/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.48  thf('86', plain,
% 0.19/0.48      ((v1_subset_1 @ sk_B @ 
% 0.19/0.48        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.19/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf('87', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A)
% 0.19/0.48        | ((sk_B)
% 0.19/0.48            = (k2_yellow19 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.48        | (v1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 0.19/0.48  thf('88', plain,
% 0.19/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | ((sk_B)
% 0.19/0.48            = (k2_yellow19 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.48        | (v2_struct_0 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['75', '87'])).
% 0.19/0.48  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('90', plain,
% 0.19/0.48      (((v1_xboole_0 @ sk_B)
% 0.19/0.48        | ((sk_B)
% 0.19/0.48            = (k2_yellow19 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.48        | (v2_struct_0 @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['88', '89'])).
% 0.19/0.48  thf('91', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('92', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | ((sk_B)
% 0.19/0.48            = (k2_yellow19 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.19/0.48      inference('clc', [status(thm)], ['90', '91'])).
% 0.19/0.48  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('94', plain,
% 0.19/0.48      (((sk_B)
% 0.19/0.48         = (k2_yellow19 @ sk_A @ 
% 0.19/0.48            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.48      inference('clc', [status(thm)], ['92', '93'])).
% 0.19/0.48  thf('95', plain,
% 0.19/0.48      ((((v1_xboole_0 @ sk_B)
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.19/0.48         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.19/0.48         <= (((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('demod', [status(thm)], ['74', '94'])).
% 0.19/0.48  thf('96', plain,
% 0.19/0.48      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ sk_B)))
% 0.19/0.48         <= (((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['95'])).
% 0.19/0.48  thf('97', plain,
% 0.19/0.48      ((((v1_xboole_0 @ sk_B)
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (v1_xboole_0 @ sk_B)
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.19/0.48         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.19/0.48         <= (((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['47', '96'])).
% 0.19/0.48  thf('98', plain,
% 0.19/0.48      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ sk_B)))
% 0.19/0.48         <= (((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['97'])).
% 0.19/0.48  thf('99', plain,
% 0.19/0.48      ((((v1_xboole_0 @ sk_B)
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (v1_xboole_0 @ sk_B)
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.19/0.48         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.19/0.48         <= (((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['30', '98'])).
% 0.19/0.48  thf('100', plain,
% 0.19/0.48      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ sk_B)))
% 0.19/0.48         <= (((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['99'])).
% 0.19/0.48  thf('101', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.19/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.48          | ~ (l1_struct_0 @ X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.19/0.48  thf('102', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.19/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.48  thf('103', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.19/0.48          | (v1_xboole_0 @ X4)
% 0.19/0.48          | ~ (l1_struct_0 @ X5)
% 0.19/0.48          | (v2_struct_0 @ X5)
% 0.19/0.48          | (v1_xboole_0 @ X6)
% 0.19/0.48          | ~ (v2_waybel_0 @ X6 @ (k3_yellow_1 @ X4))
% 0.19/0.48          | ~ (v13_waybel_0 @ X6 @ (k3_yellow_1 @ X4))
% 0.19/0.48          | ~ (m1_subset_1 @ X6 @ 
% 0.19/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X4))))
% 0.19/0.48          | ~ (v2_struct_0 @ (k3_yellow19 @ X5 @ X4 @ X6)))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.19/0.48  thf('104', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('105', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('106', plain,
% 0.19/0.48      (![X3 : $i]: ((k3_yellow_1 @ X3) = (k3_lattice3 @ (k1_lattice3 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.19/0.48  thf('107', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.19/0.48          | (v1_xboole_0 @ X4)
% 0.19/0.48          | ~ (l1_struct_0 @ X5)
% 0.19/0.48          | (v2_struct_0 @ X5)
% 0.19/0.48          | (v1_xboole_0 @ X6)
% 0.19/0.48          | ~ (v2_waybel_0 @ X6 @ (k3_lattice3 @ (k1_lattice3 @ X4)))
% 0.19/0.48          | ~ (v13_waybel_0 @ X6 @ (k3_lattice3 @ (k1_lattice3 @ X4)))
% 0.19/0.48          | ~ (m1_subset_1 @ X6 @ 
% 0.19/0.48               (k1_zfmisc_1 @ 
% 0.19/0.48                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X4)))))
% 0.19/0.48          | ~ (v2_struct_0 @ (k3_yellow19 @ X5 @ X4 @ X6)))),
% 0.19/0.48      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 0.19/0.48  thf('108', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | ~ (v13_waybel_0 @ sk_B @ 
% 0.19/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.19/0.48          | ~ (v2_waybel_0 @ sk_B @ 
% 0.19/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.19/0.48          | (v1_xboole_0 @ sk_B)
% 0.19/0.48          | (v2_struct_0 @ X0)
% 0.19/0.48          | ~ (l1_struct_0 @ X0)
% 0.19/0.48          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.19/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['102', '107'])).
% 0.19/0.48  thf('109', plain,
% 0.19/0.48      ((v13_waybel_0 @ sk_B @ 
% 0.19/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.48  thf('110', plain,
% 0.19/0.48      ((v2_waybel_0 @ sk_B @ 
% 0.19/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.19/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.48  thf('111', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | (v1_xboole_0 @ sk_B)
% 0.19/0.48          | (v2_struct_0 @ X0)
% 0.19/0.48          | ~ (l1_struct_0 @ X0)
% 0.19/0.48          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.19/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.19/0.48  thf('112', plain,
% 0.19/0.48      ((~ (l1_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A)
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['101', '111'])).
% 0.19/0.48  thf('113', plain,
% 0.19/0.48      ((~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.48      inference('simplify', [status(thm)], ['112'])).
% 0.19/0.48  thf('114', plain,
% 0.19/0.48      ((((v1_xboole_0 @ sk_B)
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.19/0.48         | ~ (l1_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ sk_B)))
% 0.19/0.48         <= (((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['100', '113'])).
% 0.19/0.48  thf('115', plain,
% 0.19/0.48      (((~ (l1_struct_0 @ sk_A)
% 0.19/0.48         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ sk_B)))
% 0.19/0.48         <= (((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['114'])).
% 0.19/0.48  thf('116', plain,
% 0.19/0.48      (((~ (l1_pre_topc @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ sk_B)
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.19/0.48         <= (((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['3', '115'])).
% 0.19/0.48  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('118', plain,
% 0.19/0.48      ((((v1_xboole_0 @ sk_B)
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.19/0.48         <= (((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('demod', [status(thm)], ['116', '117'])).
% 0.19/0.48  thf('119', plain,
% 0.19/0.48      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.19/0.48         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('120', plain,
% 0.19/0.48      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ sk_B)))
% 0.19/0.48         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.19/0.48             ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['118', '119'])).
% 0.19/0.48  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('122', plain,
% 0.19/0.48      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.19/0.48         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.19/0.48             ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('clc', [status(thm)], ['120', '121'])).
% 0.19/0.48  thf('123', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('124', plain,
% 0.19/0.48      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.19/0.48         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.19/0.48             ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('clc', [status(thm)], ['122', '123'])).
% 0.19/0.48  thf(fc5_struct_0, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.48       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.19/0.48  thf('125', plain,
% 0.19/0.48      (![X2 : $i]:
% 0.19/0.48         (~ (v1_xboole_0 @ (k2_struct_0 @ X2))
% 0.19/0.48          | ~ (l1_struct_0 @ X2)
% 0.19/0.48          | (v2_struct_0 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.19/0.48  thf('126', plain,
% 0.19/0.48      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.19/0.48         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.19/0.48             ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['124', '125'])).
% 0.19/0.48  thf('127', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('128', plain,
% 0.19/0.48      ((~ (l1_struct_0 @ sk_A))
% 0.19/0.48         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.19/0.48             ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('clc', [status(thm)], ['126', '127'])).
% 0.19/0.48  thf('129', plain,
% 0.19/0.48      ((~ (l1_pre_topc @ sk_A))
% 0.19/0.48         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.19/0.48             ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '128'])).
% 0.19/0.48  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('131', plain,
% 0.19/0.48      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.19/0.48       ~
% 0.19/0.48       ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.19/0.48      inference('demod', [status(thm)], ['129', '130'])).
% 0.19/0.48  thf('132', plain,
% 0.19/0.48      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.19/0.48       ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.19/0.48      inference('split', [status(esa)], ['65'])).
% 0.19/0.48  thf('133', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.48  thf('134', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.48  thf('135', plain,
% 0.19/0.48      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.19/0.48         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.48      inference('split', [status(esa)], ['65'])).
% 0.19/0.48  thf('136', plain,
% 0.19/0.48      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.48      inference('demod', [status(thm)], ['45', '46'])).
% 0.19/0.48  thf('137', plain,
% 0.19/0.48      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.48      inference('demod', [status(thm)], ['28', '29'])).
% 0.19/0.48  thf('138', plain,
% 0.19/0.48      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.48           sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['62', '63'])).
% 0.19/0.48  thf('139', plain,
% 0.19/0.48      (((sk_B)
% 0.19/0.48         = (k2_yellow19 @ sk_A @ 
% 0.19/0.48            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.48      inference('clc', [status(thm)], ['92', '93'])).
% 0.19/0.48  thf('140', plain,
% 0.19/0.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.48         ((v2_struct_0 @ X13)
% 0.19/0.48          | ~ (v4_orders_2 @ X13)
% 0.19/0.48          | ~ (v7_waybel_0 @ X13)
% 0.19/0.48          | ~ (l1_waybel_0 @ X13 @ X14)
% 0.19/0.48          | ~ (r1_waybel_7 @ X14 @ (k2_yellow19 @ X14 @ X13) @ X15)
% 0.19/0.48          | (r3_waybel_9 @ X14 @ X13 @ X15)
% 0.19/0.48          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.19/0.48          | ~ (l1_pre_topc @ X14)
% 0.19/0.48          | ~ (v2_pre_topc @ X14)
% 0.19/0.48          | (v2_struct_0 @ X14))),
% 0.19/0.48      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.19/0.48  thf('141', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.48          | (r3_waybel_9 @ sk_A @ 
% 0.19/0.48             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.19/0.48          | ~ (l1_waybel_0 @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.19/0.48          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['139', '140'])).
% 0.19/0.48  thf('142', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('144', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.48          | (r3_waybel_9 @ sk_A @ 
% 0.19/0.48             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.19/0.48          | ~ (l1_waybel_0 @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.19/0.48          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.48      inference('demod', [status(thm)], ['141', '142', '143'])).
% 0.19/0.48  thf('145', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ sk_B)
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | (r3_waybel_9 @ sk_A @ 
% 0.19/0.48             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['138', '144'])).
% 0.19/0.48  thf('146', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.48          | (r3_waybel_9 @ sk_A @ 
% 0.19/0.48             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.19/0.48          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | (v1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('simplify', [status(thm)], ['145'])).
% 0.19/0.48  thf('147', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ sk_B)
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48          | (v1_xboole_0 @ sk_B)
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | (r3_waybel_9 @ sk_A @ 
% 0.19/0.48             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.48          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['137', '146'])).
% 0.19/0.48  thf('148', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.48          | (r3_waybel_9 @ sk_A @ 
% 0.19/0.48             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.19/0.48          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | (v1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('simplify', [status(thm)], ['147'])).
% 0.19/0.48  thf('149', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ sk_B)
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48          | (v1_xboole_0 @ sk_B)
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | (r3_waybel_9 @ sk_A @ 
% 0.19/0.48             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.48          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['136', '148'])).
% 0.19/0.48  thf('150', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.48          | (r3_waybel_9 @ sk_A @ 
% 0.19/0.48             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.19/0.48          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48          | (v2_struct_0 @ sk_A)
% 0.19/0.48          | (v1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('simplify', [status(thm)], ['149'])).
% 0.19/0.48  thf('151', plain,
% 0.19/0.48      ((((v1_xboole_0 @ sk_B)
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48         | (r3_waybel_9 @ sk_A @ 
% 0.19/0.48            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.19/0.48         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))))
% 0.19/0.48         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['135', '150'])).
% 0.19/0.48  thf('152', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('153', plain,
% 0.19/0.48      ((((v1_xboole_0 @ sk_B)
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48         | (r3_waybel_9 @ sk_A @ 
% 0.19/0.48            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))
% 0.19/0.48         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.48      inference('demod', [status(thm)], ['151', '152'])).
% 0.19/0.48  thf('154', plain,
% 0.19/0.48      ((~ (r3_waybel_9 @ sk_A @ 
% 0.19/0.48           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.19/0.48         <= (~
% 0.19/0.48             ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('155', plain,
% 0.19/0.48      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ sk_B)))
% 0.19/0.48         <= (~
% 0.19/0.48             ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.19/0.48             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['153', '154'])).
% 0.19/0.48  thf('156', plain,
% 0.19/0.48      ((~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.19/0.48        | (v1_xboole_0 @ sk_B)
% 0.19/0.48        | (v2_struct_0 @ sk_A)
% 0.19/0.48        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.48      inference('simplify', [status(thm)], ['112'])).
% 0.19/0.48  thf('157', plain,
% 0.19/0.48      ((((v1_xboole_0 @ sk_B)
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | ~ (l1_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ sk_B)))
% 0.19/0.48         <= (~
% 0.19/0.48             ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.19/0.48             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['155', '156'])).
% 0.19/0.48  thf('158', plain,
% 0.19/0.48      (((~ (l1_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ sk_B)))
% 0.19/0.48         <= (~
% 0.19/0.48             ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.19/0.48             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['157'])).
% 0.19/0.48  thf('159', plain,
% 0.19/0.48      (((~ (l1_pre_topc @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ sk_B)
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.19/0.48         <= (~
% 0.19/0.48             ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.19/0.48             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['134', '158'])).
% 0.19/0.48  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('161', plain,
% 0.19/0.48      ((((v1_xboole_0 @ sk_B)
% 0.19/0.48         | (v2_struct_0 @ sk_A)
% 0.19/0.48         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.19/0.48         <= (~
% 0.19/0.48             ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.19/0.48             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.48      inference('demod', [status(thm)], ['159', '160'])).
% 0.19/0.48  thf('162', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('163', plain,
% 0.19/0.48      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.19/0.48         <= (~
% 0.19/0.48             ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.19/0.48             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.48      inference('clc', [status(thm)], ['161', '162'])).
% 0.19/0.48  thf('164', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('165', plain,
% 0.19/0.48      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.19/0.48         <= (~
% 0.19/0.48             ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.19/0.48             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.48      inference('clc', [status(thm)], ['163', '164'])).
% 0.19/0.48  thf('166', plain,
% 0.19/0.48      (![X2 : $i]:
% 0.19/0.48         (~ (v1_xboole_0 @ (k2_struct_0 @ X2))
% 0.19/0.48          | ~ (l1_struct_0 @ X2)
% 0.19/0.48          | (v2_struct_0 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.19/0.48  thf('167', plain,
% 0.19/0.48      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.19/0.48         <= (~
% 0.19/0.48             ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.19/0.48             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['165', '166'])).
% 0.19/0.48  thf('168', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('169', plain,
% 0.19/0.48      ((~ (l1_struct_0 @ sk_A))
% 0.19/0.48         <= (~
% 0.19/0.48             ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.19/0.48             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.48      inference('clc', [status(thm)], ['167', '168'])).
% 0.19/0.48  thf('170', plain,
% 0.19/0.48      ((~ (l1_pre_topc @ sk_A))
% 0.19/0.48         <= (~
% 0.19/0.48             ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.19/0.48             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['133', '169'])).
% 0.19/0.48  thf('171', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('172', plain,
% 0.19/0.48      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.19/0.48       ((r3_waybel_9 @ sk_A @ 
% 0.19/0.48         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.19/0.48      inference('demod', [status(thm)], ['170', '171'])).
% 0.19/0.48  thf('173', plain, ($false),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['1', '131', '132', '172'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
