%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sRa6F7YxCV

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:49 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  259 ( 764 expanded)
%              Number of leaves         :   49 ( 259 expanded)
%              Depth                    :   32
%              Number of atoms          : 3354 (14686 expanded)
%              Number of equality atoms :   49 ( 196 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

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
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X10 ) @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
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

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v4_pre_topc @ X12 @ X13 )
      | ( ( k2_pre_topc @ X13 @ X12 )
        = X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('10',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k2_pre_topc @ X15 @ X14 )
       != ( k2_struct_0 @ X15 ) )
      | ( v1_tops_1 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
       != ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v1_tops_1 @ X17 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('24',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('25',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

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

thf('26',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v1_xboole_0 @ X25 )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 )
      | ( v1_xboole_0 @ X27 )
      | ~ ( v1_subset_1 @ X27 @ ( u1_struct_0 @ ( k3_yellow_1 @ X25 ) ) )
      | ~ ( v2_waybel_0 @ X27 @ ( k3_yellow_1 @ X25 ) )
      | ~ ( v13_waybel_0 @ X27 @ ( k3_yellow_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X25 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X26 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('27',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('28',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('29',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('30',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('31',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v1_xboole_0 @ X25 )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 )
      | ( v1_xboole_0 @ X27 )
      | ~ ( v1_subset_1 @ X27 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) )
      | ~ ( v2_waybel_0 @ X27 @ ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) )
      | ~ ( v13_waybel_0 @ X27 @ ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X26 @ X25 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('32',plain,(
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
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('35',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('38',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('41',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['32','35','38','41'])).

thf('43',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['22','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('45',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('46',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['43','46','47'])).

thf('49',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('50',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

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

thf('51',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v1_xboole_0 @ X22 )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( v2_waybel_0 @ X24 @ ( k3_yellow_1 @ X22 ) )
      | ~ ( v13_waybel_0 @ X24 @ ( k3_yellow_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X22 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X23 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('52',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('53',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('54',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('55',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v1_xboole_0 @ X22 )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( v2_waybel_0 @ X24 @ ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) )
      | ~ ( v13_waybel_0 @ X24 @ ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X23 @ X22 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('58',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
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
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['49','59'])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('65',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

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

thf('66',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_xboole_0 @ X19 )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( v2_waybel_0 @ X21 @ ( k3_yellow_1 @ X19 ) )
      | ~ ( v13_waybel_0 @ X21 @ ( k3_yellow_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X19 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X20 @ X19 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('67',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('68',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('69',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('70',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_xboole_0 @ X19 )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( v2_waybel_0 @ X21 @ ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) )
      | ~ ( v13_waybel_0 @ X21 @ ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X20 @ X19 @ X21 ) @ X20 ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('73',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['64','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('77',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ),
    inference(split,[status(esa)],['79'])).

thf('81',plain,(
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

thf('82',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v7_waybel_0 @ X28 )
      | ~ ( l1_waybel_0 @ X28 @ X29 )
      | ~ ( r3_waybel_9 @ X29 @ X28 @ X30 )
      | ( r1_waybel_7 @ X29 @ ( k2_yellow19 @ X29 @ X28 ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('83',plain,(
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
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['78','87'])).

thf('89',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['63','89'])).

thf('91',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['48','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

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

thf('94',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( v1_subset_1 @ X31 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X32 ) ) ) )
      | ~ ( v2_waybel_0 @ X31 @ ( k3_yellow_1 @ ( k2_struct_0 @ X32 ) ) )
      | ~ ( v13_waybel_0 @ X31 @ ( k3_yellow_1 @ ( k2_struct_0 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X32 ) ) ) ) )
      | ( X31
        = ( k2_yellow19 @ X32 @ ( k3_yellow19 @ X32 @ ( k2_struct_0 @ X32 ) @ X31 ) ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('95',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('96',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('97',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('98',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('99',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( v1_subset_1 @ X31 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X32 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X31 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X32 ) ) ) )
      | ~ ( v13_waybel_0 @ X31 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X32 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X32 ) ) ) ) ) )
      | ( X31
        = ( k2_yellow19 @ X32 @ ( k3_yellow19 @ X32 @ ( k2_struct_0 @ X32 ) @ X31 ) ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('102',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('103',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('104',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['100','101','102','103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( sk_B_2
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ),
    inference(demod,[status(thm)],['92','109'])).

thf('111',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('113',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('114',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_xboole_0 @ X19 )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( v2_waybel_0 @ X21 @ ( k3_yellow_1 @ X19 ) )
      | ~ ( v13_waybel_0 @ X21 @ ( k3_yellow_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X19 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X20 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('115',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('116',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('117',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('118',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_xboole_0 @ X19 )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( v2_waybel_0 @ X21 @ ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) )
      | ~ ( v13_waybel_0 @ X21 @ ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X20 @ X19 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['114','115','116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf('120',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('121',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['112','122'])).

thf('124',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('125',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('126',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['111','126'])).

thf('128',plain,
    ( ( ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
   <= ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('130',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['21','134'])).

thf('136',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('139',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['135','136','137','138'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('140',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('141',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['139','142'])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','148'])).

thf('150',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('151',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ),
    inference(split,[status(esa)],['79'])).

thf('158',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('160',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
   <= ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(split,[status(esa)],['79'])).

thf('161',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('162',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['43','46','47'])).

thf('163',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('164',plain,
    ( sk_B_2
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('165',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v7_waybel_0 @ X28 )
      | ~ ( l1_waybel_0 @ X28 @ X29 )
      | ~ ( r1_waybel_7 @ X29 @ ( k2_yellow19 @ X29 @ X28 ) @ X30 )
      | ( r3_waybel_9 @ X29 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('166',plain,(
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
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,(
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
    inference('sup-',[status(thm)],['163','169'])).

thf('171',plain,(
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
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
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
    inference('sup-',[status(thm)],['162','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
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
    inference('sup-',[status(thm)],['161','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['160','175'])).

thf('177',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('180',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('182',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(clc,[status(thm)],['185','186'])).

thf('188',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['159','187'])).

thf('189',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('192',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['188','189','190','191'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('194',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(clc,[status(thm)],['197','198'])).

thf('200',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['158','199'])).

thf('201',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('202',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','156','157','207'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sRa6F7YxCV
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:49:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 306 iterations in 0.189s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.46/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.65  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.46/0.65  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.46/0.65  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.46/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.65  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.46/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.65  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.46/0.65  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.46/0.65  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.46/0.65  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.46/0.65  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.46/0.65  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.46/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.65  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.65  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.46/0.65  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.46/0.65  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.46/0.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.65  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.46/0.65  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.46/0.65  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 0.46/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.65  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.46/0.65  thf(t17_yellow19, conjecture,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.65             ( v1_subset_1 @
% 0.46/0.65               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.46/0.65             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.46/0.65             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.46/0.65             ( m1_subset_1 @
% 0.46/0.65               B @ 
% 0.46/0.65               ( k1_zfmisc_1 @
% 0.46/0.65                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.65               ( ( r3_waybel_9 @
% 0.46/0.65                   A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.46/0.65                 ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i]:
% 0.46/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.65            ( l1_pre_topc @ A ) ) =>
% 0.46/0.65          ( ![B:$i]:
% 0.46/0.65            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.65                ( v1_subset_1 @
% 0.46/0.65                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.46/0.65                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.46/0.65                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.46/0.65                ( m1_subset_1 @
% 0.46/0.65                  B @ 
% 0.46/0.65                  ( k1_zfmisc_1 @
% 0.46/0.65                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.46/0.65              ( ![C:$i]:
% 0.46/0.65                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.65                  ( ( r3_waybel_9 @
% 0.46/0.65                      A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.46/0.65                    ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t17_yellow19])).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      ((~ (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.46/0.65        | ~ (r3_waybel_9 @ sk_A @ 
% 0.46/0.65             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) | 
% 0.46/0.65       ~
% 0.46/0.65       ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf(d1_xboole_0, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.65  thf(fc4_pre_topc, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.65       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (![X10 : $i]:
% 0.46/0.65         ((v4_pre_topc @ (k2_struct_0 @ X10) @ X10)
% 0.46/0.65          | ~ (l1_pre_topc @ X10)
% 0.46/0.65          | ~ (v2_pre_topc @ X10))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.46/0.65  thf(dt_k2_struct_0, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_struct_0 @ A ) =>
% 0.46/0.65       ( m1_subset_1 @
% 0.46/0.65         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      (![X8 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (k2_struct_0 @ X8) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.46/0.65          | ~ (l1_struct_0 @ X8))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.46/0.65  thf(t52_pre_topc, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_pre_topc @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.46/0.65             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.46/0.65               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X12 : $i, X13 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.46/0.65          | ~ (v4_pre_topc @ X12 @ X13)
% 0.46/0.65          | ((k2_pre_topc @ X13 @ X12) = (X12))
% 0.46/0.65          | ~ (l1_pre_topc @ X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.46/0.65          | ~ (v4_pre_topc @ (k2_struct_0 @ X0) @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v2_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['3', '6'])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['7'])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['7'])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (![X8 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (k2_struct_0 @ X8) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.46/0.65          | ~ (l1_struct_0 @ X8))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.46/0.65  thf(d3_tops_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_pre_topc @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( ( v1_tops_1 @ B @ A ) <=>
% 0.46/0.65             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.46/0.65          | ((k2_pre_topc @ X15 @ X14) != (k2_struct_0 @ X15))
% 0.46/0.65          | (v1_tops_1 @ X14 @ X15)
% 0.46/0.65          | ~ (l1_pre_topc @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | (v1_tops_1 @ (k2_struct_0 @ X0) @ X0)
% 0.46/0.65          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) != (k2_struct_0 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.65  thf('13', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X0) != (k2_struct_0 @ X0))
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v1_tops_1 @ (k2_struct_0 @ X0) @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['9', '12'])).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_tops_1 @ (k2_struct_0 @ X0) @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['13'])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (![X8 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (k2_struct_0 @ X8) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.46/0.65          | ~ (l1_struct_0 @ X8))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.46/0.65  thf(d2_tops_3, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_pre_topc @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( ( v1_tops_1 @ B @ A ) <=>
% 0.46/0.65             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      (![X17 : $i, X18 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.65          | ~ (v1_tops_1 @ X17 @ X18)
% 0.46/0.65          | ((k2_pre_topc @ X18 @ X17) = (u1_struct_0 @ X18))
% 0.46/0.65          | ~ (l1_pre_topc @ X18))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.46/0.65          | ~ (v1_tops_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v2_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['14', '17'])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['18'])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0))
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['8', '19'])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['20'])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X8 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (k2_struct_0 @ X8) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.46/0.65          | ~ (l1_struct_0 @ X8))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B_2 @ 
% 0.46/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(d2_yellow_1, axiom,
% 0.46/0.65    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B_2 @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.46/0.65      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf(fc5_yellow19, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.46/0.65         ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.46/0.65         ( ~( v1_xboole_0 @ C ) ) & 
% 0.46/0.65         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.46/0.65         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.46/0.65         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.46/0.65         ( m1_subset_1 @
% 0.46/0.65           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.46/0.65       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.46/0.65         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.46/0.65         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.46/0.65          | (v1_xboole_0 @ X25)
% 0.46/0.65          | ~ (l1_struct_0 @ X26)
% 0.46/0.65          | (v2_struct_0 @ X26)
% 0.46/0.65          | (v1_xboole_0 @ X27)
% 0.46/0.65          | ~ (v1_subset_1 @ X27 @ (u1_struct_0 @ (k3_yellow_1 @ X25)))
% 0.46/0.65          | ~ (v2_waybel_0 @ X27 @ (k3_yellow_1 @ X25))
% 0.46/0.65          | ~ (v13_waybel_0 @ X27 @ (k3_yellow_1 @ X25))
% 0.46/0.65          | ~ (m1_subset_1 @ X27 @ 
% 0.46/0.65               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X25))))
% 0.46/0.65          | (v7_waybel_0 @ (k3_yellow19 @ X26 @ X25 @ X27)))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.46/0.65          | (v1_xboole_0 @ X25)
% 0.46/0.65          | ~ (l1_struct_0 @ X26)
% 0.46/0.65          | (v2_struct_0 @ X26)
% 0.46/0.65          | (v1_xboole_0 @ X27)
% 0.46/0.65          | ~ (v1_subset_1 @ X27 @ 
% 0.46/0.65               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X25))))
% 0.46/0.65          | ~ (v2_waybel_0 @ X27 @ (k3_lattice3 @ (k1_lattice3 @ X25)))
% 0.46/0.65          | ~ (v13_waybel_0 @ X27 @ (k3_lattice3 @ (k1_lattice3 @ X25)))
% 0.46/0.65          | ~ (m1_subset_1 @ X27 @ 
% 0.46/0.65               (k1_zfmisc_1 @ 
% 0.46/0.65                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X25)))))
% 0.46/0.65          | (v7_waybel_0 @ (k3_yellow19 @ X26 @ X25 @ X27)))),
% 0.46/0.65      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.46/0.65               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.46/0.65          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.46/0.65               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.46/0.65          | ~ (v1_subset_1 @ sk_B_2 @ 
% 0.46/0.65               (u1_struct_0 @ 
% 0.46/0.65                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.46/0.65          | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.65               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['25', '31'])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      ((v13_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      ((v13_waybel_0 @ sk_B_2 @ 
% 0.46/0.65        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      ((v2_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      ((v2_waybel_0 @ sk_B_2 @ 
% 0.46/0.65        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['36', '37'])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      ((v1_subset_1 @ sk_B_2 @ 
% 0.46/0.65        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      ((v1_subset_1 @ sk_B_2 @ 
% 0.46/0.65        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['39', '40'])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.65               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['32', '35', '38', '41'])).
% 0.46/0.65  thf('43', plain,
% 0.46/0.65      ((~ (l1_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65        | ~ (l1_struct_0 @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['22', '42'])).
% 0.46/0.65  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(dt_l1_pre_topc, axiom,
% 0.46/0.65    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.65  thf('45', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.65  thf('46', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.65  thf('47', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.46/0.65      inference('demod', [status(thm)], ['43', '46', '47'])).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      (![X8 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (k2_struct_0 @ X8) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.46/0.65          | ~ (l1_struct_0 @ X8))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.46/0.65  thf('50', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B_2 @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.46/0.65      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf(fc4_yellow19, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.46/0.65         ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.46/0.65         ( ~( v1_xboole_0 @ C ) ) & 
% 0.46/0.65         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.46/0.65         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.46/0.65         ( m1_subset_1 @
% 0.46/0.65           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.46/0.65       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.46/0.65         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.46/0.65         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.46/0.65         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.46/0.65          | (v1_xboole_0 @ X22)
% 0.46/0.65          | ~ (l1_struct_0 @ X23)
% 0.46/0.65          | (v2_struct_0 @ X23)
% 0.46/0.65          | (v1_xboole_0 @ X24)
% 0.46/0.65          | ~ (v2_waybel_0 @ X24 @ (k3_yellow_1 @ X22))
% 0.46/0.65          | ~ (v13_waybel_0 @ X24 @ (k3_yellow_1 @ X22))
% 0.46/0.65          | ~ (m1_subset_1 @ X24 @ 
% 0.46/0.65               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X22))))
% 0.46/0.65          | (v4_orders_2 @ (k3_yellow19 @ X23 @ X22 @ X24)))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.46/0.65          | (v1_xboole_0 @ X22)
% 0.46/0.65          | ~ (l1_struct_0 @ X23)
% 0.46/0.65          | (v2_struct_0 @ X23)
% 0.46/0.65          | (v1_xboole_0 @ X24)
% 0.46/0.65          | ~ (v2_waybel_0 @ X24 @ (k3_lattice3 @ (k1_lattice3 @ X22)))
% 0.46/0.65          | ~ (v13_waybel_0 @ X24 @ (k3_lattice3 @ (k1_lattice3 @ X22)))
% 0.46/0.65          | ~ (m1_subset_1 @ X24 @ 
% 0.46/0.65               (k1_zfmisc_1 @ 
% 0.46/0.65                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X22)))))
% 0.46/0.65          | (v4_orders_2 @ (k3_yellow19 @ X23 @ X22 @ X24)))),
% 0.46/0.65      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.46/0.65               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.46/0.65          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.46/0.65               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.46/0.65          | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.65               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['50', '55'])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      ((v13_waybel_0 @ sk_B_2 @ 
% 0.46/0.65        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      ((v2_waybel_0 @ sk_B_2 @ 
% 0.46/0.65        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['36', '37'])).
% 0.46/0.65  thf('59', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.65               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.46/0.65  thf('60', plain,
% 0.46/0.65      ((~ (l1_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65        | ~ (l1_struct_0 @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['49', '59'])).
% 0.46/0.65  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.65  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.65  thf('63', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.46/0.65      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.46/0.65  thf('64', plain,
% 0.46/0.65      (![X8 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (k2_struct_0 @ X8) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.46/0.65          | ~ (l1_struct_0 @ X8))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.46/0.65  thf('65', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B_2 @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.46/0.65      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf(dt_k3_yellow19, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.46/0.65         ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.46/0.65         ( ~( v1_xboole_0 @ C ) ) & 
% 0.46/0.65         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.46/0.65         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.46/0.65         ( m1_subset_1 @
% 0.46/0.65           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.46/0.65       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.46/0.65         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.46/0.65         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.46/0.65  thf('66', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.46/0.65          | (v1_xboole_0 @ X19)
% 0.46/0.65          | ~ (l1_struct_0 @ X20)
% 0.46/0.65          | (v2_struct_0 @ X20)
% 0.46/0.65          | (v1_xboole_0 @ X21)
% 0.46/0.65          | ~ (v2_waybel_0 @ X21 @ (k3_yellow_1 @ X19))
% 0.46/0.65          | ~ (v13_waybel_0 @ X21 @ (k3_yellow_1 @ X19))
% 0.46/0.65          | ~ (m1_subset_1 @ X21 @ 
% 0.46/0.65               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X19))))
% 0.46/0.65          | (l1_waybel_0 @ (k3_yellow19 @ X20 @ X19 @ X21) @ X20))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.46/0.65  thf('67', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('68', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('69', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('70', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.46/0.65          | (v1_xboole_0 @ X19)
% 0.46/0.65          | ~ (l1_struct_0 @ X20)
% 0.46/0.65          | (v2_struct_0 @ X20)
% 0.46/0.65          | (v1_xboole_0 @ X21)
% 0.46/0.65          | ~ (v2_waybel_0 @ X21 @ (k3_lattice3 @ (k1_lattice3 @ X19)))
% 0.46/0.65          | ~ (v13_waybel_0 @ X21 @ (k3_lattice3 @ (k1_lattice3 @ X19)))
% 0.46/0.65          | ~ (m1_subset_1 @ X21 @ 
% 0.46/0.65               (k1_zfmisc_1 @ 
% 0.46/0.65                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X19)))))
% 0.46/0.65          | (l1_waybel_0 @ (k3_yellow19 @ X20 @ X19 @ X21) @ X20))),
% 0.46/0.65      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.46/0.65  thf('71', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.46/0.65           X0)
% 0.46/0.65          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.46/0.65               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.46/0.65          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.46/0.65               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.46/0.65          | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.65               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['65', '70'])).
% 0.46/0.65  thf('72', plain,
% 0.46/0.65      ((v13_waybel_0 @ sk_B_2 @ 
% 0.46/0.65        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('73', plain,
% 0.46/0.65      ((v2_waybel_0 @ sk_B_2 @ 
% 0.46/0.65        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['36', '37'])).
% 0.46/0.65  thf('74', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.46/0.65           X0)
% 0.46/0.65          | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.65               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.46/0.65  thf('75', plain,
% 0.46/0.65      ((~ (l1_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65        | ~ (l1_struct_0 @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65        | (l1_waybel_0 @ 
% 0.46/0.65           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['64', '74'])).
% 0.46/0.65  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.65  thf('77', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.65  thf('78', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65        | (l1_waybel_0 @ 
% 0.46/0.65           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.46/0.65  thf('79', plain,
% 0.46/0.65      (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.46/0.65        | (r3_waybel_9 @ sk_A @ 
% 0.46/0.65           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('80', plain,
% 0.46/0.65      (((r3_waybel_9 @ sk_A @ 
% 0.46/0.65         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C))
% 0.46/0.65         <= (((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('split', [status(esa)], ['79'])).
% 0.46/0.65  thf('81', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t12_yellow19, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.46/0.65             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.65               ( ( r3_waybel_9 @ A @ B @ C ) <=>
% 0.46/0.65                 ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.46/0.65  thf('82', plain,
% 0.46/0.65      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.65         ((v2_struct_0 @ X28)
% 0.46/0.65          | ~ (v4_orders_2 @ X28)
% 0.46/0.65          | ~ (v7_waybel_0 @ X28)
% 0.46/0.65          | ~ (l1_waybel_0 @ X28 @ X29)
% 0.46/0.65          | ~ (r3_waybel_9 @ X29 @ X28 @ X30)
% 0.46/0.65          | (r1_waybel_7 @ X29 @ (k2_yellow19 @ X29 @ X28) @ X30)
% 0.46/0.65          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.46/0.65          | ~ (l1_pre_topc @ X29)
% 0.46/0.65          | ~ (v2_pre_topc @ X29)
% 0.46/0.65          | (v2_struct_0 @ X29))),
% 0.46/0.65      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.46/0.65  thf('83', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_struct_0 @ sk_A)
% 0.46/0.65          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.65          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.46/0.65          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.46/0.65          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.46/0.65          | ~ (v7_waybel_0 @ X0)
% 0.46/0.65          | ~ (v4_orders_2 @ X0)
% 0.46/0.65          | (v2_struct_0 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['81', '82'])).
% 0.46/0.65  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('86', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_struct_0 @ sk_A)
% 0.46/0.65          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.46/0.65          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.46/0.65          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.46/0.65          | ~ (v7_waybel_0 @ X0)
% 0.46/0.65          | ~ (v4_orders_2 @ X0)
% 0.46/0.65          | (v2_struct_0 @ X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.46/0.65  thf('87', plain,
% 0.46/0.65      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65         | ~ (v4_orders_2 @ 
% 0.46/0.65              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65         | ~ (v7_waybel_0 @ 
% 0.46/0.65              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65         | ~ (l1_waybel_0 @ 
% 0.46/0.65              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.46/0.65         | (r1_waybel_7 @ sk_A @ 
% 0.46/0.65            (k2_yellow19 @ sk_A @ 
% 0.46/0.65             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)) @ 
% 0.46/0.65            sk_C)
% 0.46/0.65         | (v2_struct_0 @ sk_A)))
% 0.46/0.65         <= (((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['80', '86'])).
% 0.46/0.65  thf('88', plain,
% 0.46/0.65      ((((v1_xboole_0 @ sk_B_2)
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (r1_waybel_7 @ sk_A @ 
% 0.46/0.65            (k2_yellow19 @ sk_A @ 
% 0.46/0.65             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)) @ 
% 0.46/0.65            sk_C)
% 0.46/0.65         | ~ (v7_waybel_0 @ 
% 0.46/0.65              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65         | ~ (v4_orders_2 @ 
% 0.46/0.65              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))
% 0.46/0.65         <= (((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['78', '87'])).
% 0.46/0.65  thf('89', plain,
% 0.46/0.65      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65         | ~ (v4_orders_2 @ 
% 0.46/0.65              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65         | ~ (v7_waybel_0 @ 
% 0.46/0.65              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65         | (r1_waybel_7 @ sk_A @ 
% 0.46/0.65            (k2_yellow19 @ sk_A @ 
% 0.46/0.65             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)) @ 
% 0.46/0.65            sk_C)
% 0.46/0.65         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ sk_B_2)))
% 0.46/0.65         <= (((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['88'])).
% 0.46/0.65  thf('90', plain,
% 0.46/0.65      ((((v1_xboole_0 @ sk_B_2)
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65         | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65         | (r1_waybel_7 @ sk_A @ 
% 0.46/0.65            (k2_yellow19 @ sk_A @ 
% 0.46/0.65             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)) @ 
% 0.46/0.65            sk_C)
% 0.46/0.65         | ~ (v7_waybel_0 @ 
% 0.46/0.65              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))
% 0.46/0.65         <= (((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['63', '89'])).
% 0.46/0.65  thf('91', plain,
% 0.46/0.65      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65         | ~ (v7_waybel_0 @ 
% 0.46/0.65              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65         | (r1_waybel_7 @ sk_A @ 
% 0.46/0.65            (k2_yellow19 @ sk_A @ 
% 0.46/0.65             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)) @ 
% 0.46/0.65            sk_C)
% 0.46/0.65         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ sk_B_2)))
% 0.46/0.65         <= (((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['90'])).
% 0.46/0.65  thf('92', plain,
% 0.46/0.65      ((((v1_xboole_0 @ sk_B_2)
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65         | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65         | (r1_waybel_7 @ sk_A @ 
% 0.46/0.65            (k2_yellow19 @ sk_A @ 
% 0.46/0.65             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)) @ 
% 0.46/0.65            sk_C)
% 0.46/0.65         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))
% 0.46/0.65         <= (((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['48', '91'])).
% 0.46/0.65  thf('93', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B_2 @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.46/0.65      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf(t15_yellow19, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.65             ( v1_subset_1 @
% 0.46/0.65               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.46/0.65             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.46/0.65             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.46/0.65             ( m1_subset_1 @
% 0.46/0.65               B @ 
% 0.46/0.65               ( k1_zfmisc_1 @
% 0.46/0.65                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.46/0.65           ( ( B ) =
% 0.46/0.65             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.46/0.65  thf('94', plain,
% 0.46/0.65      (![X31 : $i, X32 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X31)
% 0.46/0.65          | ~ (v1_subset_1 @ X31 @ 
% 0.46/0.65               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X32))))
% 0.46/0.65          | ~ (v2_waybel_0 @ X31 @ (k3_yellow_1 @ (k2_struct_0 @ X32)))
% 0.46/0.65          | ~ (v13_waybel_0 @ X31 @ (k3_yellow_1 @ (k2_struct_0 @ X32)))
% 0.46/0.65          | ~ (m1_subset_1 @ X31 @ 
% 0.46/0.65               (k1_zfmisc_1 @ 
% 0.46/0.65                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X32)))))
% 0.46/0.65          | ((X31)
% 0.46/0.65              = (k2_yellow19 @ X32 @ 
% 0.46/0.65                 (k3_yellow19 @ X32 @ (k2_struct_0 @ X32) @ X31)))
% 0.46/0.65          | ~ (l1_struct_0 @ X32)
% 0.46/0.65          | (v2_struct_0 @ X32))),
% 0.46/0.65      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.46/0.65  thf('95', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('96', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('97', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('98', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('99', plain,
% 0.46/0.65      (![X31 : $i, X32 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ X31)
% 0.46/0.65          | ~ (v1_subset_1 @ X31 @ 
% 0.46/0.65               (u1_struct_0 @ 
% 0.46/0.65                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X32)))))
% 0.46/0.65          | ~ (v2_waybel_0 @ X31 @ 
% 0.46/0.65               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X32))))
% 0.46/0.65          | ~ (v13_waybel_0 @ X31 @ 
% 0.46/0.65               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X32))))
% 0.46/0.65          | ~ (m1_subset_1 @ X31 @ 
% 0.46/0.65               (k1_zfmisc_1 @ 
% 0.46/0.65                (u1_struct_0 @ 
% 0.46/0.65                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X32))))))
% 0.46/0.65          | ((X31)
% 0.46/0.65              = (k2_yellow19 @ X32 @ 
% 0.46/0.65                 (k3_yellow19 @ X32 @ (k2_struct_0 @ X32) @ X31)))
% 0.46/0.65          | ~ (l1_struct_0 @ X32)
% 0.46/0.65          | (v2_struct_0 @ X32))),
% 0.46/0.65      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 0.46/0.65  thf('100', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_A)
% 0.46/0.65        | ~ (l1_struct_0 @ sk_A)
% 0.46/0.65        | ((sk_B_2)
% 0.46/0.65            = (k2_yellow19 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.46/0.65        | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.46/0.65             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.46/0.65        | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.46/0.65             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.46/0.65        | ~ (v1_subset_1 @ sk_B_2 @ 
% 0.46/0.65             (u1_struct_0 @ 
% 0.46/0.65              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.46/0.65        | (v1_xboole_0 @ sk_B_2))),
% 0.46/0.65      inference('sup-', [status(thm)], ['93', '99'])).
% 0.46/0.65  thf('101', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.65  thf('102', plain,
% 0.46/0.65      ((v13_waybel_0 @ sk_B_2 @ 
% 0.46/0.65        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('103', plain,
% 0.46/0.65      ((v2_waybel_0 @ sk_B_2 @ 
% 0.46/0.65        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['36', '37'])).
% 0.46/0.65  thf('104', plain,
% 0.46/0.65      ((v1_subset_1 @ sk_B_2 @ 
% 0.46/0.65        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['39', '40'])).
% 0.46/0.65  thf('105', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_A)
% 0.46/0.65        | ((sk_B_2)
% 0.46/0.65            = (k2_yellow19 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.46/0.65        | (v1_xboole_0 @ sk_B_2))),
% 0.46/0.65      inference('demod', [status(thm)], ['100', '101', '102', '103', '104'])).
% 0.46/0.65  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('107', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_B_2)
% 0.46/0.65        | ((sk_B_2)
% 0.46/0.65            = (k2_yellow19 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))),
% 0.46/0.65      inference('clc', [status(thm)], ['105', '106'])).
% 0.46/0.65  thf('108', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('109', plain,
% 0.46/0.65      (((sk_B_2)
% 0.46/0.65         = (k2_yellow19 @ sk_A @ 
% 0.46/0.65            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.46/0.65      inference('clc', [status(thm)], ['107', '108'])).
% 0.46/0.65  thf('110', plain,
% 0.46/0.65      ((((v1_xboole_0 @ sk_B_2)
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65         | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.46/0.65         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))
% 0.46/0.65         <= (((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('demod', [status(thm)], ['92', '109'])).
% 0.46/0.65  thf('111', plain,
% 0.46/0.65      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.46/0.65         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ sk_B_2)))
% 0.46/0.65         <= (((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['110'])).
% 0.46/0.65  thf('112', plain,
% 0.46/0.65      (![X8 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (k2_struct_0 @ X8) @ 
% 0.46/0.65           (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.46/0.65          | ~ (l1_struct_0 @ X8))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.46/0.65  thf('113', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B_2 @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.46/0.65      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf('114', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.46/0.65          | (v1_xboole_0 @ X19)
% 0.46/0.65          | ~ (l1_struct_0 @ X20)
% 0.46/0.65          | (v2_struct_0 @ X20)
% 0.46/0.65          | (v1_xboole_0 @ X21)
% 0.46/0.65          | ~ (v2_waybel_0 @ X21 @ (k3_yellow_1 @ X19))
% 0.46/0.65          | ~ (v13_waybel_0 @ X21 @ (k3_yellow_1 @ X19))
% 0.46/0.65          | ~ (m1_subset_1 @ X21 @ 
% 0.46/0.65               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X19))))
% 0.46/0.65          | ~ (v2_struct_0 @ (k3_yellow19 @ X20 @ X19 @ X21)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.46/0.65  thf('115', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('116', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('117', plain,
% 0.46/0.65      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.65  thf('118', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.46/0.65          | (v1_xboole_0 @ X19)
% 0.46/0.65          | ~ (l1_struct_0 @ X20)
% 0.46/0.65          | (v2_struct_0 @ X20)
% 0.46/0.65          | (v1_xboole_0 @ X21)
% 0.46/0.65          | ~ (v2_waybel_0 @ X21 @ (k3_lattice3 @ (k1_lattice3 @ X19)))
% 0.46/0.65          | ~ (v13_waybel_0 @ X21 @ (k3_lattice3 @ (k1_lattice3 @ X19)))
% 0.46/0.65          | ~ (m1_subset_1 @ X21 @ 
% 0.46/0.65               (k1_zfmisc_1 @ 
% 0.46/0.65                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X19)))))
% 0.46/0.65          | ~ (v2_struct_0 @ (k3_yellow19 @ X20 @ X19 @ X21)))),
% 0.46/0.65      inference('demod', [status(thm)], ['114', '115', '116', '117'])).
% 0.46/0.65  thf('119', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.46/0.65               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.46/0.65          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.46/0.65               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.46/0.65          | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.65               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['113', '118'])).
% 0.46/0.65  thf('120', plain,
% 0.46/0.65      ((v13_waybel_0 @ sk_B_2 @ 
% 0.46/0.65        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('121', plain,
% 0.46/0.65      ((v2_waybel_0 @ sk_B_2 @ 
% 0.46/0.65        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.65      inference('demod', [status(thm)], ['36', '37'])).
% 0.46/0.65  thf('122', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65          | (v2_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_struct_0 @ X0)
% 0.46/0.65          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.65               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.46/0.65  thf('123', plain,
% 0.46/0.65      ((~ (l1_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65        | ~ (l1_struct_0 @ sk_A)
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['112', '122'])).
% 0.46/0.65  thf('124', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.65  thf('125', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.65  thf('126', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.46/0.65      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.46/0.65  thf('127', plain,
% 0.46/0.65      ((((v1_xboole_0 @ sk_B_2)
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.46/0.65         | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.46/0.65         <= (((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['111', '126'])).
% 0.46/0.65  thf('128', plain,
% 0.46/0.65      ((((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)
% 0.46/0.65         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ sk_B_2)))
% 0.46/0.65         <= (((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['127'])).
% 0.46/0.65  thf('129', plain,
% 0.46/0.65      ((~ (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C))
% 0.46/0.65         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf('130', plain,
% 0.46/0.65      ((((v1_xboole_0 @ sk_B_2)
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.46/0.65         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['128', '129'])).
% 0.46/0.65  thf('131', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('132', plain,
% 0.46/0.65      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.46/0.65         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('clc', [status(thm)], ['130', '131'])).
% 0.46/0.65  thf('133', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('134', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.46/0.65         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('clc', [status(thm)], ['132', '133'])).
% 0.46/0.65  thf('135', plain,
% 0.46/0.65      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65         | ~ (v2_pre_topc @ sk_A)
% 0.46/0.65         | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65         | ~ (l1_struct_0 @ sk_A)))
% 0.46/0.65         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['21', '134'])).
% 0.46/0.65  thf('136', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('138', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.65  thf('139', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('demod', [status(thm)], ['135', '136', '137', '138'])).
% 0.46/0.65  thf(rc7_pre_topc, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.65       ( ?[B:$i]:
% 0.46/0.65         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.65           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.65  thf('140', plain,
% 0.46/0.65      (![X11 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (sk_B_1 @ X11) @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.46/0.65          | ~ (l1_pre_topc @ X11)
% 0.46/0.65          | ~ (v2_pre_topc @ X11)
% 0.46/0.65          | (v2_struct_0 @ X11))),
% 0.46/0.65      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.46/0.65  thf(t5_subset, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.46/0.65          ( v1_xboole_0 @ C ) ) ))).
% 0.46/0.65  thf('141', plain,
% 0.46/0.65      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X5 @ X6)
% 0.46/0.65          | ~ (v1_xboole_0 @ X7)
% 0.46/0.65          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t5_subset])).
% 0.46/0.65  thf('142', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((v2_struct_0 @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.46/0.65          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['140', '141'])).
% 0.46/0.65  thf('143', plain,
% 0.46/0.65      ((![X0 : $i]:
% 0.46/0.65          (~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A))
% 0.46/0.65           | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65           | ~ (v2_pre_topc @ sk_A)
% 0.46/0.65           | (v2_struct_0 @ sk_A)))
% 0.46/0.65         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['139', '142'])).
% 0.46/0.65  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('145', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('146', plain,
% 0.46/0.65      ((![X0 : $i]:
% 0.46/0.65          (~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.46/0.65         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.46/0.65  thf('147', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('148', plain,
% 0.46/0.65      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A)))
% 0.46/0.65         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('clc', [status(thm)], ['146', '147'])).
% 0.46/0.65  thf('149', plain,
% 0.46/0.65      (((v1_xboole_0 @ (sk_B_1 @ sk_A)))
% 0.46/0.65         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['2', '148'])).
% 0.46/0.65  thf('150', plain,
% 0.46/0.65      (![X11 : $i]:
% 0.46/0.65         (~ (v1_xboole_0 @ (sk_B_1 @ X11))
% 0.46/0.65          | ~ (l1_pre_topc @ X11)
% 0.46/0.65          | ~ (v2_pre_topc @ X11)
% 0.46/0.65          | (v2_struct_0 @ X11))),
% 0.46/0.65      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.46/0.65  thf('151', plain,
% 0.46/0.65      ((((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.46/0.65         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['149', '150'])).
% 0.46/0.65  thf('152', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('153', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('154', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_A))
% 0.46/0.65         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) & 
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('demod', [status(thm)], ['151', '152', '153'])).
% 0.46/0.65  thf('155', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('156', plain,
% 0.46/0.65      (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) | 
% 0.46/0.65       ~
% 0.46/0.65       ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['154', '155'])).
% 0.46/0.65  thf('157', plain,
% 0.46/0.65      (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) | 
% 0.46/0.65       ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C))),
% 0.46/0.65      inference('split', [status(esa)], ['79'])).
% 0.46/0.65  thf('158', plain,
% 0.46/0.65      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.65  thf('159', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_struct_0 @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['20'])).
% 0.46/0.65  thf('160', plain,
% 0.46/0.65      (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C))
% 0.46/0.65         <= (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.46/0.65      inference('split', [status(esa)], ['79'])).
% 0.46/0.65  thf('161', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.46/0.65      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.46/0.65  thf('162', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.46/0.65      inference('demod', [status(thm)], ['43', '46', '47'])).
% 0.46/0.65  thf('163', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65        | (l1_waybel_0 @ 
% 0.46/0.65           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.46/0.65  thf('164', plain,
% 0.46/0.65      (((sk_B_2)
% 0.46/0.65         = (k2_yellow19 @ sk_A @ 
% 0.46/0.65            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.46/0.65      inference('clc', [status(thm)], ['107', '108'])).
% 0.46/0.65  thf('165', plain,
% 0.46/0.65      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.65         ((v2_struct_0 @ X28)
% 0.46/0.65          | ~ (v4_orders_2 @ X28)
% 0.46/0.65          | ~ (v7_waybel_0 @ X28)
% 0.46/0.65          | ~ (l1_waybel_0 @ X28 @ X29)
% 0.46/0.65          | ~ (r1_waybel_7 @ X29 @ (k2_yellow19 @ X29 @ X28) @ X30)
% 0.46/0.65          | (r3_waybel_9 @ X29 @ X28 @ X30)
% 0.46/0.65          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.46/0.65          | ~ (l1_pre_topc @ X29)
% 0.46/0.65          | ~ (v2_pre_topc @ X29)
% 0.46/0.65          | (v2_struct_0 @ X29))),
% 0.46/0.65      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.46/0.65  thf('166', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.65          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | (r3_waybel_9 @ sk_A @ 
% 0.46/0.65             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 0.46/0.65          | ~ (l1_waybel_0 @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.46/0.65          | ~ (v7_waybel_0 @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | ~ (v4_orders_2 @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['164', '165'])).
% 0.46/0.65  thf('167', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('169', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | (r3_waybel_9 @ sk_A @ 
% 0.46/0.65             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 0.46/0.65          | ~ (l1_waybel_0 @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.46/0.65          | ~ (v7_waybel_0 @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | ~ (v4_orders_2 @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.46/0.65      inference('demod', [status(thm)], ['166', '167', '168'])).
% 0.46/0.65  thf('170', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ sk_B_2)
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | ~ (v4_orders_2 @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | ~ (v7_waybel_0 @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | (r3_waybel_9 @ sk_A @ 
% 0.46/0.65             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | ~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['163', '169'])).
% 0.46/0.65  thf('171', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | (r3_waybel_9 @ sk_A @ 
% 0.46/0.65             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 0.46/0.65          | ~ (v7_waybel_0 @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | ~ (v4_orders_2 @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | (v1_xboole_0 @ sk_B_2))),
% 0.46/0.65      inference('simplify', [status(thm)], ['170'])).
% 0.46/0.65  thf('172', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ sk_B_2)
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65          | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | ~ (v4_orders_2 @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | (r3_waybel_9 @ sk_A @ 
% 0.46/0.65             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | ~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['162', '171'])).
% 0.46/0.65  thf('173', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | (r3_waybel_9 @ sk_A @ 
% 0.46/0.65             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 0.46/0.65          | ~ (v4_orders_2 @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | (v1_xboole_0 @ sk_B_2))),
% 0.46/0.65      inference('simplify', [status(thm)], ['172'])).
% 0.46/0.65  thf('174', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ sk_B_2)
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65          | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | (r3_waybel_9 @ sk_A @ 
% 0.46/0.65             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | ~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['161', '173'])).
% 0.46/0.65  thf('175', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65          | (r3_waybel_9 @ sk_A @ 
% 0.46/0.65             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 0.46/0.65          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65          | (v2_struct_0 @ sk_A)
% 0.46/0.65          | (v1_xboole_0 @ sk_B_2))),
% 0.46/0.65      inference('simplify', [status(thm)], ['174'])).
% 0.46/0.65  thf('176', plain,
% 0.46/0.65      ((((v1_xboole_0 @ sk_B_2)
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65         | (r3_waybel_9 @ sk_A @ 
% 0.46/0.65            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)
% 0.46/0.65         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))))
% 0.46/0.65         <= (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['160', '175'])).
% 0.46/0.65  thf('177', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('178', plain,
% 0.46/0.65      ((((v1_xboole_0 @ sk_B_2)
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65         | (r3_waybel_9 @ sk_A @ 
% 0.46/0.65            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))
% 0.46/0.65         <= (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.46/0.65      inference('demod', [status(thm)], ['176', '177'])).
% 0.46/0.65  thf('179', plain,
% 0.46/0.65      ((~ (r3_waybel_9 @ sk_A @ 
% 0.46/0.65           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C))
% 0.46/0.65         <= (~
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf('180', plain,
% 0.46/0.65      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.46/0.65         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ sk_B_2)))
% 0.46/0.65         <= (~
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)) & 
% 0.46/0.65             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['178', '179'])).
% 0.46/0.65  thf('181', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.46/0.65      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.46/0.65  thf('182', plain,
% 0.46/0.65      ((((v1_xboole_0 @ sk_B_2)
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65         | (v1_xboole_0 @ sk_B_2)
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.46/0.65         <= (~
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)) & 
% 0.46/0.65             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['180', '181'])).
% 0.46/0.65  thf('183', plain,
% 0.46/0.65      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.65         | (v2_struct_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ sk_B_2)))
% 0.46/0.65         <= (~
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)) & 
% 0.46/0.65             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['182'])).
% 0.46/0.65  thf('184', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('185', plain,
% 0.46/0.65      ((((v1_xboole_0 @ sk_B_2) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.46/0.65         <= (~
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)) & 
% 0.46/0.65             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.46/0.65      inference('clc', [status(thm)], ['183', '184'])).
% 0.46/0.65  thf('186', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('187', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.46/0.65         <= (~
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)) & 
% 0.46/0.65             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.46/0.65      inference('clc', [status(thm)], ['185', '186'])).
% 0.46/0.65  thf('188', plain,
% 0.46/0.65      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.65         | ~ (v2_pre_topc @ sk_A)
% 0.46/0.65         | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65         | ~ (l1_struct_0 @ sk_A)))
% 0.46/0.65         <= (~
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)) & 
% 0.46/0.65             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['159', '187'])).
% 0.46/0.65  thf('189', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('190', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('191', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.65  thf('192', plain,
% 0.46/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65         <= (~
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)) & 
% 0.46/0.65             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.46/0.65      inference('demod', [status(thm)], ['188', '189', '190', '191'])).
% 0.46/0.65  thf('193', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((v2_struct_0 @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.46/0.65          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['140', '141'])).
% 0.46/0.65  thf('194', plain,
% 0.46/0.65      ((![X0 : $i]:
% 0.46/0.65          (~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A))
% 0.46/0.65           | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65           | ~ (v2_pre_topc @ sk_A)
% 0.46/0.65           | (v2_struct_0 @ sk_A)))
% 0.46/0.65         <= (~
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)) & 
% 0.46/0.65             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['192', '193'])).
% 0.46/0.65  thf('195', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('196', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('197', plain,
% 0.46/0.65      ((![X0 : $i]:
% 0.46/0.65          (~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.46/0.65         <= (~
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)) & 
% 0.46/0.65             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.46/0.65      inference('demod', [status(thm)], ['194', '195', '196'])).
% 0.46/0.65  thf('198', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('199', plain,
% 0.46/0.65      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A)))
% 0.46/0.65         <= (~
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)) & 
% 0.46/0.65             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.46/0.65      inference('clc', [status(thm)], ['197', '198'])).
% 0.46/0.65  thf('200', plain,
% 0.46/0.65      (((v1_xboole_0 @ (sk_B_1 @ sk_A)))
% 0.46/0.65         <= (~
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)) & 
% 0.46/0.65             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['158', '199'])).
% 0.46/0.65  thf('201', plain,
% 0.46/0.65      (![X11 : $i]:
% 0.46/0.65         (~ (v1_xboole_0 @ (sk_B_1 @ X11))
% 0.46/0.65          | ~ (l1_pre_topc @ X11)
% 0.46/0.65          | ~ (v2_pre_topc @ X11)
% 0.46/0.65          | (v2_struct_0 @ X11))),
% 0.46/0.65      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.46/0.65  thf('202', plain,
% 0.46/0.65      ((((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.46/0.65         <= (~
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)) & 
% 0.46/0.65             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['200', '201'])).
% 0.46/0.65  thf('203', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('204', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('205', plain,
% 0.46/0.65      (((v2_struct_0 @ sk_A))
% 0.46/0.65         <= (~
% 0.46/0.65             ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C)) & 
% 0.46/0.65             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.46/0.65      inference('demod', [status(thm)], ['202', '203', '204'])).
% 0.46/0.65  thf('206', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('207', plain,
% 0.46/0.65      (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C)) | 
% 0.46/0.65       ((r3_waybel_9 @ sk_A @ 
% 0.46/0.65         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['205', '206'])).
% 0.46/0.65  thf('208', plain, ($false),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['1', '156', '157', '207'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
