%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jxjc9lXuBy

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:50 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  255 ( 685 expanded)
%              Number of leaves         :   44 ( 228 expanded)
%              Depth                    :   35
%              Number of atoms          : 3444 (13186 expanded)
%              Number of equality atoms :   51 ( 200 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

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

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X5 ) @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

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

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v4_pre_topc @ X6 @ X7 )
      | ( ( k2_pre_topc @ X7 @ X6 )
        = X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k2_pre_topc @ X9 @ X8 )
       != ( k2_struct_0 @ X9 ) )
      | ( v1_tops_1 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
       != ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v1_tops_1 @ X11 @ X12 )
      | ( ( k2_pre_topc @ X12 @ X11 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('24',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('25',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('27',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

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

thf('29',plain,(
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

thf('30',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('31',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('32',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('33',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('34',plain,(
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
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
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
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('38',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('41',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('44',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['35','38','41','44'])).

thf('46',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','45'])).

thf('47',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('52',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

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

thf('54',plain,(
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

thf('55',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('56',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('57',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('58',plain,(
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
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('61',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','62'])).

thf('64',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('69',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

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

thf('71',plain,(
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

thf('72',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('73',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('74',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('75',plain,(
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
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('78',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['69','79'])).

thf('81',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['68','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['85'])).

thf('87',plain,(
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

thf('88',plain,(
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

thf('89',plain,(
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
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['86','92'])).

thf('94',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['84','93'])).

thf('95',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
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
    inference('sup-',[status(thm)],['67','95'])).

thf('97',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['50','97'])).

thf('99',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

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

thf('101',plain,(
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

thf('102',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

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
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['100','106'])).

thf('108',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('109',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('110',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['107','108','109','110'])).

thf('112',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['98','118'])).

thf('120',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('122',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('123',plain,(
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

thf('124',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('125',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('126',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('127',plain,(
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
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['122','127'])).

thf('129',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('130',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['121','131'])).

thf('133',plain,
    ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['120','133'])).

thf('135',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['23','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('140',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['22','144'])).

thf('146',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','148'])).

thf('150',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('152',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('153',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','155'])).

thf('157',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['85'])).

thf('160',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('161',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('163',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('164',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['85'])).

thf('165',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('166',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('167',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('168',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('169',plain,(
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

thf('170',plain,(
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
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,(
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
    inference('sup-',[status(thm)],['167','173'])).

thf('175',plain,(
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
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
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
    inference('sup-',[status(thm)],['166','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
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
    inference('sup-',[status(thm)],['165','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['164','179'])).

thf('181',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('184',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,
    ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['132'])).

thf('186',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['163','187'])).

thf('189',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('193',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['162','194'])).

thf('196',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['161','198'])).

thf('200',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('203',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['203','204'])).

thf('206',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['160','205'])).

thf('207',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','158','159','208'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jxjc9lXuBy
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.61  % Solved by: fo/fo7.sh
% 0.38/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.61  % done 287 iterations in 0.134s
% 0.38/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.61  % SZS output start Refutation
% 0.38/0.61  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.38/0.61  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.38/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.61  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.38/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.61  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.38/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.61  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.38/0.61  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.38/0.61  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.38/0.61  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.38/0.61  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.38/0.61  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 0.38/0.61  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.38/0.61  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.38/0.61  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.38/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.61  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.38/0.61  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.38/0.61  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.38/0.61  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.38/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.61  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.38/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.61  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.38/0.61  thf(t17_yellow19, conjecture,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.61             ( v1_subset_1 @
% 0.38/0.61               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.38/0.61             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.61             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.61             ( m1_subset_1 @
% 0.38/0.61               B @ 
% 0.38/0.61               ( k1_zfmisc_1 @
% 0.38/0.61                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.38/0.61           ( ![C:$i]:
% 0.38/0.61             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.61               ( ( r3_waybel_9 @
% 0.38/0.61                   A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.38/0.61                 ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.38/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.61    (~( ![A:$i]:
% 0.38/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.61            ( l1_pre_topc @ A ) ) =>
% 0.38/0.61          ( ![B:$i]:
% 0.38/0.61            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.61                ( v1_subset_1 @
% 0.38/0.61                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.38/0.61                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.61                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.61                ( m1_subset_1 @
% 0.38/0.61                  B @ 
% 0.38/0.61                  ( k1_zfmisc_1 @
% 0.38/0.61                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.38/0.61              ( ![C:$i]:
% 0.38/0.61                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.61                  ( ( r3_waybel_9 @
% 0.38/0.61                      A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.38/0.61                    ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.38/0.61    inference('cnf.neg', [status(esa)], [t17_yellow19])).
% 0.38/0.61  thf('0', plain,
% 0.38/0.61      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.61        | ~ (r3_waybel_9 @ sk_A @ 
% 0.38/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('1', plain,
% 0.38/0.61      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.38/0.61       ~
% 0.38/0.61       ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.38/0.61      inference('split', [status(esa)], ['0'])).
% 0.38/0.61  thf(dt_l1_pre_topc, axiom,
% 0.38/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.61  thf('2', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.61  thf('3', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.61  thf(fc4_pre_topc, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.61       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.38/0.61  thf('4', plain,
% 0.38/0.61      (![X5 : $i]:
% 0.38/0.61         ((v4_pre_topc @ (k2_struct_0 @ X5) @ X5)
% 0.38/0.61          | ~ (l1_pre_topc @ X5)
% 0.38/0.61          | ~ (v2_pre_topc @ X5))),
% 0.38/0.61      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.38/0.61  thf(dt_k2_struct_0, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( l1_struct_0 @ A ) =>
% 0.38/0.61       ( m1_subset_1 @
% 0.38/0.61         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.61  thf('5', plain,
% 0.38/0.61      (![X2 : $i]:
% 0.38/0.61         ((m1_subset_1 @ (k2_struct_0 @ X2) @ 
% 0.38/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.38/0.61          | ~ (l1_struct_0 @ X2))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.38/0.61  thf(t52_pre_topc, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( l1_pre_topc @ A ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.38/0.61             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.38/0.61               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.38/0.61  thf('6', plain,
% 0.38/0.61      (![X6 : $i, X7 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.38/0.61          | ~ (v4_pre_topc @ X6 @ X7)
% 0.38/0.61          | ((k2_pre_topc @ X7 @ X6) = (X6))
% 0.38/0.61          | ~ (l1_pre_topc @ X7))),
% 0.38/0.61      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.38/0.61  thf('7', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.38/0.61          | ~ (v4_pre_topc @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.61  thf('8', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['4', '7'])).
% 0.38/0.61  thf('9', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ X0)
% 0.38/0.61          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['8'])).
% 0.38/0.61  thf('10', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ X0)
% 0.38/0.61          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['8'])).
% 0.38/0.61  thf('11', plain,
% 0.38/0.61      (![X2 : $i]:
% 0.38/0.61         ((m1_subset_1 @ (k2_struct_0 @ X2) @ 
% 0.38/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.38/0.61          | ~ (l1_struct_0 @ X2))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.38/0.61  thf(d3_tops_1, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( l1_pre_topc @ A ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61           ( ( v1_tops_1 @ B @ A ) <=>
% 0.38/0.61             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.61  thf('12', plain,
% 0.38/0.61      (![X8 : $i, X9 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.38/0.61          | ((k2_pre_topc @ X9 @ X8) != (k2_struct_0 @ X9))
% 0.38/0.61          | (v1_tops_1 @ X8 @ X9)
% 0.38/0.61          | ~ (l1_pre_topc @ X9))),
% 0.38/0.61      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.38/0.61  thf('13', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | (v1_tops_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.61          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) != (k2_struct_0 @ X0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.61  thf('14', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k2_struct_0 @ X0) != (k2_struct_0 @ X0))
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | (v1_tops_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['10', '13'])).
% 0.38/0.61  thf('15', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v1_tops_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['14'])).
% 0.38/0.61  thf('16', plain,
% 0.38/0.61      (![X2 : $i]:
% 0.38/0.61         ((m1_subset_1 @ (k2_struct_0 @ X2) @ 
% 0.38/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.38/0.61          | ~ (l1_struct_0 @ X2))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.38/0.61  thf(d2_tops_3, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( l1_pre_topc @ A ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.61           ( ( v1_tops_1 @ B @ A ) <=>
% 0.38/0.61             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.61  thf('17', plain,
% 0.38/0.61      (![X11 : $i, X12 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.38/0.61          | ~ (v1_tops_1 @ X11 @ X12)
% 0.38/0.61          | ((k2_pre_topc @ X12 @ X11) = (u1_struct_0 @ X12))
% 0.38/0.61          | ~ (l1_pre_topc @ X12))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.38/0.61  thf('18', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v1_tops_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.61  thf('19', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['15', '18'])).
% 0.38/0.61  thf('20', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['19'])).
% 0.38/0.61  thf('21', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0))
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['9', '20'])).
% 0.38/0.61  thf('22', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['21'])).
% 0.38/0.61  thf('23', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.61  thf('24', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.61  thf('25', plain,
% 0.38/0.61      (![X2 : $i]:
% 0.38/0.61         ((m1_subset_1 @ (k2_struct_0 @ X2) @ 
% 0.38/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.38/0.61          | ~ (l1_struct_0 @ X2))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.38/0.61  thf('26', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ 
% 0.38/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(d2_yellow_1, axiom,
% 0.38/0.61    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.38/0.61  thf('27', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('28', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.61  thf(fc5_yellow19, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.38/0.61         ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.38/0.61         ( ~( v1_xboole_0 @ C ) ) & 
% 0.38/0.61         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.38/0.61         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.38/0.61         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.38/0.61         ( m1_subset_1 @
% 0.38/0.61           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.38/0.61       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.38/0.61         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.38/0.61         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.38/0.61  thf('29', plain,
% 0.38/0.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.38/0.61          | (v1_xboole_0 @ X19)
% 0.38/0.61          | ~ (l1_struct_0 @ X20)
% 0.38/0.61          | (v2_struct_0 @ X20)
% 0.38/0.61          | (v1_xboole_0 @ X21)
% 0.38/0.61          | ~ (v1_subset_1 @ X21 @ (u1_struct_0 @ (k3_yellow_1 @ X19)))
% 0.38/0.61          | ~ (v2_waybel_0 @ X21 @ (k3_yellow_1 @ X19))
% 0.38/0.61          | ~ (v13_waybel_0 @ X21 @ (k3_yellow_1 @ X19))
% 0.38/0.61          | ~ (m1_subset_1 @ X21 @ 
% 0.38/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X19))))
% 0.38/0.61          | (v7_waybel_0 @ (k3_yellow19 @ X20 @ X19 @ X21)))),
% 0.38/0.61      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.38/0.61  thf('30', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('31', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('32', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('33', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('34', plain,
% 0.38/0.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.38/0.61          | (v1_xboole_0 @ X19)
% 0.38/0.61          | ~ (l1_struct_0 @ X20)
% 0.38/0.61          | (v2_struct_0 @ X20)
% 0.38/0.61          | (v1_xboole_0 @ X21)
% 0.38/0.61          | ~ (v1_subset_1 @ X21 @ 
% 0.38/0.61               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X19))))
% 0.38/0.61          | ~ (v2_waybel_0 @ X21 @ (k3_lattice3 @ (k1_lattice3 @ X19)))
% 0.38/0.61          | ~ (v13_waybel_0 @ X21 @ (k3_lattice3 @ (k1_lattice3 @ X19)))
% 0.38/0.61          | ~ (m1_subset_1 @ X21 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X19)))))
% 0.38/0.61          | (v7_waybel_0 @ (k3_yellow19 @ X20 @ X19 @ X21)))),
% 0.38/0.61      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.38/0.61  thf('35', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | ~ (v13_waybel_0 @ sk_B @ 
% 0.38/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.61          | ~ (v2_waybel_0 @ sk_B @ 
% 0.38/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.61          | ~ (v1_subset_1 @ sk_B @ 
% 0.38/0.61               (u1_struct_0 @ 
% 0.38/0.61                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.61          | (v1_xboole_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['28', '34'])).
% 0.38/0.61  thf('36', plain,
% 0.38/0.61      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('37', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('38', plain,
% 0.38/0.61      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.61      inference('demod', [status(thm)], ['36', '37'])).
% 0.38/0.61  thf('39', plain,
% 0.38/0.61      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('40', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('41', plain,
% 0.38/0.61      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.61      inference('demod', [status(thm)], ['39', '40'])).
% 0.38/0.61  thf('42', plain,
% 0.38/0.61      ((v1_subset_1 @ sk_B @ 
% 0.38/0.61        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('43', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('44', plain,
% 0.38/0.61      ((v1_subset_1 @ sk_B @ 
% 0.38/0.61        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.38/0.61      inference('demod', [status(thm)], ['42', '43'])).
% 0.38/0.61  thf('45', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | (v1_xboole_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.61      inference('demod', [status(thm)], ['35', '38', '41', '44'])).
% 0.38/0.61  thf('46', plain,
% 0.38/0.61      ((~ (l1_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ sk_B)
% 0.38/0.61        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['25', '45'])).
% 0.38/0.61  thf('47', plain,
% 0.38/0.61      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61        | (v1_xboole_0 @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.61      inference('simplify', [status(thm)], ['46'])).
% 0.38/0.61  thf('48', plain,
% 0.38/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61        | (v2_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ sk_B)
% 0.38/0.61        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['24', '47'])).
% 0.38/0.61  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('50', plain,
% 0.38/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61        | (v2_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ sk_B)
% 0.38/0.61        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.61      inference('demod', [status(thm)], ['48', '49'])).
% 0.38/0.61  thf('51', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.61  thf('52', plain,
% 0.38/0.61      (![X2 : $i]:
% 0.38/0.61         ((m1_subset_1 @ (k2_struct_0 @ X2) @ 
% 0.38/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.38/0.61          | ~ (l1_struct_0 @ X2))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.38/0.61  thf('53', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.61  thf(fc4_yellow19, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.38/0.61         ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.38/0.61         ( ~( v1_xboole_0 @ C ) ) & 
% 0.38/0.61         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.38/0.61         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.38/0.61         ( m1_subset_1 @
% 0.38/0.61           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.38/0.61       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.38/0.61         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.38/0.61         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.38/0.61         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.38/0.61  thf('54', plain,
% 0.38/0.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.38/0.61          | (v1_xboole_0 @ X16)
% 0.38/0.61          | ~ (l1_struct_0 @ X17)
% 0.38/0.61          | (v2_struct_0 @ X17)
% 0.38/0.61          | (v1_xboole_0 @ X18)
% 0.38/0.61          | ~ (v2_waybel_0 @ X18 @ (k3_yellow_1 @ X16))
% 0.38/0.61          | ~ (v13_waybel_0 @ X18 @ (k3_yellow_1 @ X16))
% 0.38/0.61          | ~ (m1_subset_1 @ X18 @ 
% 0.38/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X16))))
% 0.38/0.61          | (v4_orders_2 @ (k3_yellow19 @ X17 @ X16 @ X18)))),
% 0.38/0.61      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.38/0.61  thf('55', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('56', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('57', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('58', plain,
% 0.38/0.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.38/0.61          | (v1_xboole_0 @ X16)
% 0.38/0.61          | ~ (l1_struct_0 @ X17)
% 0.38/0.61          | (v2_struct_0 @ X17)
% 0.38/0.61          | (v1_xboole_0 @ X18)
% 0.38/0.61          | ~ (v2_waybel_0 @ X18 @ (k3_lattice3 @ (k1_lattice3 @ X16)))
% 0.38/0.61          | ~ (v13_waybel_0 @ X18 @ (k3_lattice3 @ (k1_lattice3 @ X16)))
% 0.38/0.61          | ~ (m1_subset_1 @ X18 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X16)))))
% 0.38/0.61          | (v4_orders_2 @ (k3_yellow19 @ X17 @ X16 @ X18)))),
% 0.38/0.61      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.38/0.61  thf('59', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | ~ (v13_waybel_0 @ sk_B @ 
% 0.38/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.61          | ~ (v2_waybel_0 @ sk_B @ 
% 0.38/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.61          | (v1_xboole_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['53', '58'])).
% 0.38/0.61  thf('60', plain,
% 0.38/0.61      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.61      inference('demod', [status(thm)], ['36', '37'])).
% 0.38/0.61  thf('61', plain,
% 0.38/0.61      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.61      inference('demod', [status(thm)], ['39', '40'])).
% 0.38/0.61  thf('62', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | (v1_xboole_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.61      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.38/0.61  thf('63', plain,
% 0.38/0.61      ((~ (l1_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ sk_B)
% 0.38/0.61        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['52', '62'])).
% 0.38/0.61  thf('64', plain,
% 0.38/0.61      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61        | (v1_xboole_0 @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.61      inference('simplify', [status(thm)], ['63'])).
% 0.38/0.61  thf('65', plain,
% 0.38/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61        | (v2_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ sk_B)
% 0.38/0.61        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['51', '64'])).
% 0.38/0.61  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('67', plain,
% 0.38/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61        | (v2_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ sk_B)
% 0.38/0.61        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.61      inference('demod', [status(thm)], ['65', '66'])).
% 0.38/0.61  thf('68', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.61  thf('69', plain,
% 0.38/0.61      (![X2 : $i]:
% 0.38/0.61         ((m1_subset_1 @ (k2_struct_0 @ X2) @ 
% 0.38/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.38/0.61          | ~ (l1_struct_0 @ X2))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.38/0.61  thf('70', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.61  thf(dt_k3_yellow19, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.38/0.61         ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.38/0.61         ( ~( v1_xboole_0 @ C ) ) & 
% 0.38/0.61         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.38/0.61         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.38/0.61         ( m1_subset_1 @
% 0.38/0.61           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.38/0.61       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.38/0.61         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.38/0.61         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.38/0.61  thf('71', plain,
% 0.38/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.38/0.61          | (v1_xboole_0 @ X13)
% 0.38/0.61          | ~ (l1_struct_0 @ X14)
% 0.38/0.61          | (v2_struct_0 @ X14)
% 0.38/0.61          | (v1_xboole_0 @ X15)
% 0.38/0.61          | ~ (v2_waybel_0 @ X15 @ (k3_yellow_1 @ X13))
% 0.38/0.61          | ~ (v13_waybel_0 @ X15 @ (k3_yellow_1 @ X13))
% 0.38/0.61          | ~ (m1_subset_1 @ X15 @ 
% 0.38/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X13))))
% 0.38/0.61          | (l1_waybel_0 @ (k3_yellow19 @ X14 @ X13 @ X15) @ X14))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.38/0.61  thf('72', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('73', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('74', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('75', plain,
% 0.38/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.38/0.61          | (v1_xboole_0 @ X13)
% 0.38/0.61          | ~ (l1_struct_0 @ X14)
% 0.38/0.61          | (v2_struct_0 @ X14)
% 0.38/0.61          | (v1_xboole_0 @ X15)
% 0.38/0.61          | ~ (v2_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.38/0.61          | ~ (v13_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.38/0.61          | ~ (m1_subset_1 @ X15 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X13)))))
% 0.38/0.61          | (l1_waybel_0 @ (k3_yellow19 @ X14 @ X13 @ X15) @ X14))),
% 0.38/0.61      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.38/0.61  thf('76', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.61          | ~ (v13_waybel_0 @ sk_B @ 
% 0.38/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.61          | ~ (v2_waybel_0 @ sk_B @ 
% 0.38/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.61          | (v1_xboole_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['70', '75'])).
% 0.38/0.61  thf('77', plain,
% 0.38/0.61      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.61      inference('demod', [status(thm)], ['36', '37'])).
% 0.38/0.61  thf('78', plain,
% 0.38/0.61      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.61      inference('demod', [status(thm)], ['39', '40'])).
% 0.38/0.61  thf('79', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.61          | (v1_xboole_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.61      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.38/0.61  thf('80', plain,
% 0.38/0.61      ((~ (l1_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ sk_B)
% 0.38/0.61        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.61           sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['69', '79'])).
% 0.38/0.61  thf('81', plain,
% 0.38/0.61      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.61         sk_A)
% 0.38/0.61        | (v1_xboole_0 @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.61      inference('simplify', [status(thm)], ['80'])).
% 0.38/0.61  thf('82', plain,
% 0.38/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61        | (v2_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ sk_B)
% 0.38/0.61        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.61           sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['68', '81'])).
% 0.38/0.61  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('84', plain,
% 0.38/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61        | (v2_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ sk_B)
% 0.38/0.61        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.61           sk_A))),
% 0.38/0.61      inference('demod', [status(thm)], ['82', '83'])).
% 0.38/0.61  thf('85', plain,
% 0.38/0.61      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.61        | (r3_waybel_9 @ sk_A @ 
% 0.38/0.61           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('86', plain,
% 0.38/0.61      (((r3_waybel_9 @ sk_A @ 
% 0.38/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.38/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('split', [status(esa)], ['85'])).
% 0.38/0.61  thf('87', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t12_yellow19, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.38/0.61             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.38/0.61           ( ![C:$i]:
% 0.38/0.61             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.61               ( ( r3_waybel_9 @ A @ B @ C ) <=>
% 0.38/0.61                 ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.38/0.61  thf('88', plain,
% 0.38/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.61         ((v2_struct_0 @ X22)
% 0.38/0.61          | ~ (v4_orders_2 @ X22)
% 0.38/0.61          | ~ (v7_waybel_0 @ X22)
% 0.38/0.61          | ~ (l1_waybel_0 @ X22 @ X23)
% 0.38/0.61          | ~ (r3_waybel_9 @ X23 @ X22 @ X24)
% 0.38/0.61          | (r1_waybel_7 @ X23 @ (k2_yellow19 @ X23 @ X22) @ X24)
% 0.38/0.61          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.38/0.61          | ~ (l1_pre_topc @ X23)
% 0.38/0.61          | ~ (v2_pre_topc @ X23)
% 0.38/0.61          | (v2_struct_0 @ X23))),
% 0.38/0.61      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.38/0.61  thf('89', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v2_struct_0 @ sk_A)
% 0.38/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.61          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.38/0.61          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.38/0.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.38/0.61          | ~ (v7_waybel_0 @ X0)
% 0.38/0.61          | ~ (v4_orders_2 @ X0)
% 0.38/0.61          | (v2_struct_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['87', '88'])).
% 0.38/0.61  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('92', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v2_struct_0 @ sk_A)
% 0.38/0.61          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.38/0.61          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.38/0.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.38/0.61          | ~ (v7_waybel_0 @ X0)
% 0.38/0.61          | ~ (v4_orders_2 @ X0)
% 0.38/0.61          | (v2_struct_0 @ X0))),
% 0.38/0.61      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.38/0.61  thf('93', plain,
% 0.38/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61         | ~ (l1_waybel_0 @ 
% 0.38/0.61              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.38/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.38/0.61            (k2_yellow19 @ sk_A @ 
% 0.38/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.38/0.61            sk_C)
% 0.38/0.61         | (v2_struct_0 @ sk_A)))
% 0.38/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['86', '92'])).
% 0.38/0.61  thf('94', plain,
% 0.38/0.61      ((((v1_xboole_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.38/0.61            (k2_yellow19 @ sk_A @ 
% 0.38/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.38/0.61            sk_C)
% 0.38/0.61         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.38/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['84', '93'])).
% 0.38/0.61  thf('95', plain,
% 0.38/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.38/0.61            (k2_yellow19 @ sk_A @ 
% 0.38/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.38/0.61            sk_C)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ sk_B)))
% 0.38/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['94'])).
% 0.38/0.61  thf('96', plain,
% 0.38/0.61      ((((v1_xboole_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (v1_xboole_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.38/0.61            (k2_yellow19 @ sk_A @ 
% 0.38/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.38/0.61            sk_C)
% 0.38/0.61         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.38/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['67', '95'])).
% 0.38/0.61  thf('97', plain,
% 0.38/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.38/0.61            (k2_yellow19 @ sk_A @ 
% 0.38/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.38/0.61            sk_C)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ sk_B)))
% 0.38/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['96'])).
% 0.38/0.61  thf('98', plain,
% 0.38/0.61      ((((v1_xboole_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (v1_xboole_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.38/0.61            (k2_yellow19 @ sk_A @ 
% 0.38/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.38/0.61            sk_C)
% 0.38/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.38/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['50', '97'])).
% 0.38/0.61  thf('99', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.61  thf('100', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.61  thf(t15_yellow19, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.61       ( ![B:$i]:
% 0.38/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.61             ( v1_subset_1 @
% 0.38/0.61               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.38/0.61             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.61             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.61             ( m1_subset_1 @
% 0.38/0.61               B @ 
% 0.38/0.61               ( k1_zfmisc_1 @
% 0.38/0.61                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.38/0.61           ( ( B ) =
% 0.38/0.61             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.38/0.61  thf('101', plain,
% 0.38/0.61      (![X25 : $i, X26 : $i]:
% 0.38/0.61         ((v1_xboole_0 @ X25)
% 0.38/0.61          | ~ (v1_subset_1 @ X25 @ 
% 0.38/0.61               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X26))))
% 0.38/0.61          | ~ (v2_waybel_0 @ X25 @ (k3_yellow_1 @ (k2_struct_0 @ X26)))
% 0.38/0.61          | ~ (v13_waybel_0 @ X25 @ (k3_yellow_1 @ (k2_struct_0 @ X26)))
% 0.38/0.61          | ~ (m1_subset_1 @ X25 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X26)))))
% 0.38/0.61          | ((X25)
% 0.38/0.61              = (k2_yellow19 @ X26 @ 
% 0.38/0.61                 (k3_yellow19 @ X26 @ (k2_struct_0 @ X26) @ X25)))
% 0.38/0.61          | ~ (l1_struct_0 @ X26)
% 0.38/0.61          | (v2_struct_0 @ X26))),
% 0.38/0.61      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.38/0.61  thf('102', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('103', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('104', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('105', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('106', plain,
% 0.38/0.61      (![X25 : $i, X26 : $i]:
% 0.38/0.61         ((v1_xboole_0 @ X25)
% 0.38/0.61          | ~ (v1_subset_1 @ X25 @ 
% 0.38/0.61               (u1_struct_0 @ 
% 0.38/0.61                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X26)))))
% 0.38/0.61          | ~ (v2_waybel_0 @ X25 @ 
% 0.38/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X26))))
% 0.38/0.61          | ~ (v13_waybel_0 @ X25 @ 
% 0.38/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X26))))
% 0.38/0.61          | ~ (m1_subset_1 @ X25 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (u1_struct_0 @ 
% 0.38/0.61                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X26))))))
% 0.38/0.61          | ((X25)
% 0.38/0.61              = (k2_yellow19 @ X26 @ 
% 0.38/0.61                 (k3_yellow19 @ X26 @ (k2_struct_0 @ X26) @ X25)))
% 0.38/0.61          | ~ (l1_struct_0 @ X26)
% 0.38/0.61          | (v2_struct_0 @ X26))),
% 0.38/0.61      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 0.38/0.61  thf('107', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.61        | ((sk_B)
% 0.38/0.61            = (k2_yellow19 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.61        | ~ (v13_waybel_0 @ sk_B @ 
% 0.38/0.61             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.61        | ~ (v2_waybel_0 @ sk_B @ 
% 0.38/0.61             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.61        | ~ (v1_subset_1 @ sk_B @ 
% 0.38/0.61             (u1_struct_0 @ 
% 0.38/0.61              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.61        | (v1_xboole_0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['100', '106'])).
% 0.38/0.61  thf('108', plain,
% 0.38/0.61      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.61      inference('demod', [status(thm)], ['36', '37'])).
% 0.38/0.61  thf('109', plain,
% 0.38/0.61      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.61      inference('demod', [status(thm)], ['39', '40'])).
% 0.38/0.61  thf('110', plain,
% 0.38/0.61      ((v1_subset_1 @ sk_B @ 
% 0.38/0.61        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.38/0.61      inference('demod', [status(thm)], ['42', '43'])).
% 0.38/0.61  thf('111', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.61        | ((sk_B)
% 0.38/0.61            = (k2_yellow19 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.61        | (v1_xboole_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['107', '108', '109', '110'])).
% 0.38/0.61  thf('112', plain,
% 0.38/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ sk_B)
% 0.38/0.61        | ((sk_B)
% 0.38/0.61            = (k2_yellow19 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.61        | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['99', '111'])).
% 0.38/0.61  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('114', plain,
% 0.38/0.61      (((v1_xboole_0 @ sk_B)
% 0.38/0.61        | ((sk_B)
% 0.38/0.61            = (k2_yellow19 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.61        | (v2_struct_0 @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)], ['112', '113'])).
% 0.38/0.61  thf('115', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('116', plain,
% 0.38/0.61      (((v2_struct_0 @ sk_A)
% 0.38/0.61        | ((sk_B)
% 0.38/0.61            = (k2_yellow19 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.38/0.61      inference('clc', [status(thm)], ['114', '115'])).
% 0.38/0.61  thf('117', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('118', plain,
% 0.38/0.61      (((sk_B)
% 0.38/0.61         = (k2_yellow19 @ sk_A @ 
% 0.38/0.61            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['116', '117'])).
% 0.38/0.61  thf('119', plain,
% 0.38/0.61      ((((v1_xboole_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (v1_xboole_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.38/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('demod', [status(thm)], ['98', '118'])).
% 0.38/0.61  thf('120', plain,
% 0.38/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ sk_B)))
% 0.38/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['119'])).
% 0.38/0.61  thf('121', plain,
% 0.38/0.61      (![X2 : $i]:
% 0.38/0.61         ((m1_subset_1 @ (k2_struct_0 @ X2) @ 
% 0.38/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.38/0.61          | ~ (l1_struct_0 @ X2))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.38/0.61  thf('122', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_B @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.61  thf('123', plain,
% 0.38/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.38/0.61          | (v1_xboole_0 @ X13)
% 0.38/0.61          | ~ (l1_struct_0 @ X14)
% 0.38/0.61          | (v2_struct_0 @ X14)
% 0.38/0.61          | (v1_xboole_0 @ X15)
% 0.38/0.61          | ~ (v2_waybel_0 @ X15 @ (k3_yellow_1 @ X13))
% 0.38/0.61          | ~ (v13_waybel_0 @ X15 @ (k3_yellow_1 @ X13))
% 0.38/0.61          | ~ (m1_subset_1 @ X15 @ 
% 0.38/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X13))))
% 0.38/0.61          | ~ (v2_struct_0 @ (k3_yellow19 @ X14 @ X13 @ X15)))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.38/0.61  thf('124', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('125', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('126', plain,
% 0.38/0.61      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.61  thf('127', plain,
% 0.38/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.38/0.61          | (v1_xboole_0 @ X13)
% 0.38/0.61          | ~ (l1_struct_0 @ X14)
% 0.38/0.61          | (v2_struct_0 @ X14)
% 0.38/0.61          | (v1_xboole_0 @ X15)
% 0.38/0.61          | ~ (v2_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.38/0.61          | ~ (v13_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.38/0.61          | ~ (m1_subset_1 @ X15 @ 
% 0.38/0.61               (k1_zfmisc_1 @ 
% 0.38/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X13)))))
% 0.38/0.61          | ~ (v2_struct_0 @ (k3_yellow19 @ X14 @ X13 @ X15)))),
% 0.38/0.61      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 0.38/0.61  thf('128', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | ~ (v13_waybel_0 @ sk_B @ 
% 0.38/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.61          | ~ (v2_waybel_0 @ sk_B @ 
% 0.38/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.61          | (v1_xboole_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['122', '127'])).
% 0.38/0.61  thf('129', plain,
% 0.38/0.61      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.61      inference('demod', [status(thm)], ['36', '37'])).
% 0.38/0.61  thf('130', plain,
% 0.38/0.61      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.61      inference('demod', [status(thm)], ['39', '40'])).
% 0.38/0.61  thf('131', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | (v1_xboole_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_struct_0 @ X0)
% 0.38/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.61      inference('demod', [status(thm)], ['128', '129', '130'])).
% 0.38/0.61  thf('132', plain,
% 0.38/0.61      ((~ (l1_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.61        | (v2_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ sk_B)
% 0.38/0.61        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['121', '131'])).
% 0.38/0.61  thf('133', plain,
% 0.38/0.61      ((~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61        | (v1_xboole_0 @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.61      inference('simplify', [status(thm)], ['132'])).
% 0.38/0.61  thf('134', plain,
% 0.38/0.61      ((((v1_xboole_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.61         | ~ (l1_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ sk_B)))
% 0.38/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['120', '133'])).
% 0.38/0.61  thf('135', plain,
% 0.38/0.61      (((~ (l1_struct_0 @ sk_A)
% 0.38/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ sk_B)))
% 0.38/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['134'])).
% 0.38/0.61  thf('136', plain,
% 0.38/0.61      (((~ (l1_pre_topc @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.38/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['23', '135'])).
% 0.38/0.61  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('138', plain,
% 0.38/0.61      ((((v1_xboole_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.38/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('demod', [status(thm)], ['136', '137'])).
% 0.38/0.61  thf('139', plain,
% 0.38/0.61      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.38/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.61      inference('split', [status(esa)], ['0'])).
% 0.38/0.61  thf('140', plain,
% 0.38/0.61      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ sk_B)))
% 0.38/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['138', '139'])).
% 0.38/0.61  thf('141', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('142', plain,
% 0.38/0.61      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.38/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('clc', [status(thm)], ['140', '141'])).
% 0.38/0.61  thf('143', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('144', plain,
% 0.38/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.38/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('clc', [status(thm)], ['142', '143'])).
% 0.38/0.61  thf('145', plain,
% 0.38/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.61         | ~ (v2_pre_topc @ sk_A)
% 0.38/0.61         | ~ (l1_pre_topc @ sk_A)
% 0.38/0.61         | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['22', '144'])).
% 0.38/0.61  thf('146', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('148', plain,
% 0.38/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('demod', [status(thm)], ['145', '146', '147'])).
% 0.38/0.61  thf('149', plain,
% 0.38/0.61      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['3', '148'])).
% 0.38/0.61  thf('150', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('151', plain,
% 0.38/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('demod', [status(thm)], ['149', '150'])).
% 0.38/0.61  thf(fc2_struct_0, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.61       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.61  thf('152', plain,
% 0.38/0.61      (![X4 : $i]:
% 0.38/0.61         (~ (v1_xboole_0 @ (u1_struct_0 @ X4))
% 0.38/0.61          | ~ (l1_struct_0 @ X4)
% 0.38/0.61          | (v2_struct_0 @ X4))),
% 0.38/0.61      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.61  thf('153', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['151', '152'])).
% 0.38/0.61  thf('154', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('155', plain,
% 0.38/0.61      ((~ (l1_struct_0 @ sk_A))
% 0.38/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('clc', [status(thm)], ['153', '154'])).
% 0.38/0.61  thf('156', plain,
% 0.38/0.61      ((~ (l1_pre_topc @ sk_A))
% 0.38/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['2', '155'])).
% 0.38/0.61  thf('157', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('158', plain,
% 0.38/0.61      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.38/0.61       ~
% 0.38/0.61       ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.38/0.61      inference('demod', [status(thm)], ['156', '157'])).
% 0.38/0.61  thf('159', plain,
% 0.38/0.61      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.38/0.61       ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.38/0.61      inference('split', [status(esa)], ['85'])).
% 0.38/0.61  thf('160', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.61  thf('161', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.61  thf('162', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (l1_struct_0 @ X0)
% 0.38/0.61          | ~ (l1_pre_topc @ X0)
% 0.38/0.61          | ~ (v2_pre_topc @ X0)
% 0.38/0.61          | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['21'])).
% 0.38/0.61  thf('163', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.38/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.61  thf('164', plain,
% 0.38/0.61      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.38/0.61         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.61      inference('split', [status(esa)], ['85'])).
% 0.38/0.61  thf('165', plain,
% 0.38/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61        | (v2_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ sk_B)
% 0.38/0.61        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.61      inference('demod', [status(thm)], ['65', '66'])).
% 0.38/0.61  thf('166', plain,
% 0.38/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61        | (v2_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ sk_B)
% 0.38/0.61        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.61      inference('demod', [status(thm)], ['48', '49'])).
% 0.38/0.61  thf('167', plain,
% 0.38/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61        | (v2_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ sk_B)
% 0.38/0.61        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.61           sk_A))),
% 0.38/0.61      inference('demod', [status(thm)], ['82', '83'])).
% 0.38/0.61  thf('168', plain,
% 0.38/0.61      (((sk_B)
% 0.38/0.61         = (k2_yellow19 @ sk_A @ 
% 0.38/0.61            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.61      inference('clc', [status(thm)], ['116', '117'])).
% 0.38/0.61  thf('169', plain,
% 0.38/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.61         ((v2_struct_0 @ X22)
% 0.38/0.61          | ~ (v4_orders_2 @ X22)
% 0.38/0.61          | ~ (v7_waybel_0 @ X22)
% 0.38/0.61          | ~ (l1_waybel_0 @ X22 @ X23)
% 0.38/0.61          | ~ (r1_waybel_7 @ X23 @ (k2_yellow19 @ X23 @ X22) @ X24)
% 0.38/0.61          | (r3_waybel_9 @ X23 @ X22 @ X24)
% 0.38/0.61          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.38/0.61          | ~ (l1_pre_topc @ X23)
% 0.38/0.61          | ~ (v2_pre_topc @ X23)
% 0.38/0.61          | (v2_struct_0 @ X23))),
% 0.38/0.61      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.38/0.61  thf('170', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_A)
% 0.38/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.38/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.61          | ~ (l1_waybel_0 @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.38/0.61          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['168', '169'])).
% 0.38/0.61  thf('171', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('172', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('173', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.61          | (v2_struct_0 @ sk_A)
% 0.38/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.38/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.61          | ~ (l1_waybel_0 @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.38/0.61          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.61      inference('demod', [status(thm)], ['170', '171', '172'])).
% 0.38/0.61  thf('174', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v1_xboole_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ sk_A)
% 0.38/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.38/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.61          | (v2_struct_0 @ sk_A)
% 0.38/0.61          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['167', '173'])).
% 0.38/0.61  thf('175', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.38/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.61          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61          | (v2_struct_0 @ sk_A)
% 0.38/0.61          | (v1_xboole_0 @ sk_B))),
% 0.38/0.61      inference('simplify', [status(thm)], ['174'])).
% 0.38/0.61  thf('176', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v1_xboole_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ sk_A)
% 0.38/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61          | (v1_xboole_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ sk_A)
% 0.38/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.38/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.61          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['166', '175'])).
% 0.38/0.61  thf('177', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.38/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.61          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61          | (v2_struct_0 @ sk_A)
% 0.38/0.61          | (v1_xboole_0 @ sk_B))),
% 0.38/0.61      inference('simplify', [status(thm)], ['176'])).
% 0.38/0.61  thf('178', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((v1_xboole_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ sk_A)
% 0.38/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61          | (v1_xboole_0 @ sk_B)
% 0.38/0.61          | (v2_struct_0 @ sk_A)
% 0.38/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.38/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.61          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['165', '177'])).
% 0.38/0.61  thf('179', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.38/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61          | (v2_struct_0 @ sk_A)
% 0.38/0.61          | (v1_xboole_0 @ sk_B))),
% 0.38/0.61      inference('simplify', [status(thm)], ['178'])).
% 0.38/0.61  thf('180', plain,
% 0.38/0.61      ((((v1_xboole_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61         | (r3_waybel_9 @ sk_A @ 
% 0.38/0.61            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.38/0.61         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))))
% 0.38/0.61         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['164', '179'])).
% 0.38/0.61  thf('181', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('182', plain,
% 0.38/0.61      ((((v1_xboole_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61         | (r3_waybel_9 @ sk_A @ 
% 0.38/0.61            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))
% 0.38/0.61         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.61      inference('demod', [status(thm)], ['180', '181'])).
% 0.38/0.61  thf('183', plain,
% 0.38/0.61      ((~ (r3_waybel_9 @ sk_A @ 
% 0.38/0.61           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.38/0.61         <= (~
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.38/0.61      inference('split', [status(esa)], ['0'])).
% 0.38/0.61  thf('184', plain,
% 0.38/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ sk_B)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['182', '183'])).
% 0.38/0.61  thf('185', plain,
% 0.38/0.61      ((~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.61        | (v1_xboole_0 @ sk_B)
% 0.38/0.61        | (v2_struct_0 @ sk_A)
% 0.38/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.61      inference('simplify', [status(thm)], ['132'])).
% 0.38/0.61  thf('186', plain,
% 0.38/0.61      ((((v1_xboole_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | ~ (l1_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ sk_B)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['184', '185'])).
% 0.38/0.61  thf('187', plain,
% 0.38/0.61      (((~ (l1_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ sk_B)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['186'])).
% 0.38/0.61  thf('188', plain,
% 0.38/0.61      (((~ (l1_pre_topc @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.38/0.61         <= (~
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['163', '187'])).
% 0.38/0.61  thf('189', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('190', plain,
% 0.38/0.61      ((((v1_xboole_0 @ sk_B)
% 0.38/0.61         | (v2_struct_0 @ sk_A)
% 0.38/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.38/0.61         <= (~
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.61      inference('demod', [status(thm)], ['188', '189'])).
% 0.38/0.61  thf('191', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('192', plain,
% 0.38/0.61      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.61      inference('clc', [status(thm)], ['190', '191'])).
% 0.38/0.61  thf('193', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('194', plain,
% 0.38/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.61      inference('clc', [status(thm)], ['192', '193'])).
% 0.38/0.61  thf('195', plain,
% 0.38/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.61         | ~ (v2_pre_topc @ sk_A)
% 0.38/0.61         | ~ (l1_pre_topc @ sk_A)
% 0.38/0.61         | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['162', '194'])).
% 0.38/0.61  thf('196', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('197', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('198', plain,
% 0.38/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.61      inference('demod', [status(thm)], ['195', '196', '197'])).
% 0.38/0.61  thf('199', plain,
% 0.38/0.61      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.61         <= (~
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['161', '198'])).
% 0.38/0.61  thf('200', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('201', plain,
% 0.38/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.61      inference('demod', [status(thm)], ['199', '200'])).
% 0.38/0.61  thf('202', plain,
% 0.38/0.61      (![X4 : $i]:
% 0.38/0.61         (~ (v1_xboole_0 @ (u1_struct_0 @ X4))
% 0.38/0.61          | ~ (l1_struct_0 @ X4)
% 0.38/0.61          | (v2_struct_0 @ X4))),
% 0.38/0.61      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.61  thf('203', plain,
% 0.38/0.61      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.61         <= (~
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['201', '202'])).
% 0.38/0.61  thf('204', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('205', plain,
% 0.38/0.61      ((~ (l1_struct_0 @ sk_A))
% 0.38/0.61         <= (~
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.61      inference('clc', [status(thm)], ['203', '204'])).
% 0.38/0.61  thf('206', plain,
% 0.38/0.61      ((~ (l1_pre_topc @ sk_A))
% 0.38/0.61         <= (~
% 0.38/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.38/0.61             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['160', '205'])).
% 0.38/0.61  thf('207', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('208', plain,
% 0.38/0.61      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.38/0.61       ((r3_waybel_9 @ sk_A @ 
% 0.38/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.38/0.61      inference('demod', [status(thm)], ['206', '207'])).
% 0.38/0.61  thf('209', plain, ($false),
% 0.38/0.61      inference('sat_resolution*', [status(thm)], ['1', '158', '159', '208'])).
% 0.38/0.61  
% 0.38/0.61  % SZS output end Refutation
% 0.38/0.61  
% 0.38/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
