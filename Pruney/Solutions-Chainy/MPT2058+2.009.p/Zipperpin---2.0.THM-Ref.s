%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lc6914mXMf

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:49 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  354 ( 883 expanded)
%              Number of leaves         :   50 ( 296 expanded)
%              Depth                    :   36
%              Number of atoms          : 4364 (15822 expanded)
%              Number of equality atoms :   49 ( 213 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X10 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('5',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('6',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('8',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('9',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('10',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('11',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    r1_tarski @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_tarski @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

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

thf('20',plain,(
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

thf('21',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('22',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('23',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('24',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('25',plain,(
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
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('28',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('31',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('40',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('46',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('49',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['26','35','44','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['6','54'])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('61',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

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

thf('62',plain,(
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

thf('63',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('64',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('65',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('66',plain,(
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
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('69',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['60','70'])).

thf('72',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('76',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('77',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

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

thf('78',plain,(
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
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('85',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['76','86'])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('92',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['93'])).

thf('95',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['92','94'])).

thf('96',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['91','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
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

thf('100',plain,(
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

thf('101',plain,(
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
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C_1 )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C_1 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['98','104'])).

thf('106',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) @ sk_C_1 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['90','105'])).

thf('107',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) @ sk_C_1 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['74','107'])).

thf('109',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('110',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('111',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('112',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('113',plain,(
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

thf('114',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('115',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('116',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('117',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('118',plain,(
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
    inference(demod,[status(thm)],['113','114','115','116','117'])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['112','118'])).

thf('120',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('121',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('122',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('124',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( sk_B_2
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['110','130'])).

thf('132',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_2
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['109','131'])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( sk_B_2
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['108','134'])).

thf('136',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['58','136'])).

thf('138',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('140',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('141',plain,(
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

thf('142',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('143',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('144',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('145',plain,(
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
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['140','145'])).

thf('147',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('148',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['139','149'])).

thf('151',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['138','150'])).

thf('152',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','152'])).

thf('154',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
   <= ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('157',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['159','160'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('162',plain,(
    ! [X16: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('163',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('165',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('168',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['164','169'])).

thf('171',plain,
    ( ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['161','170'])).

thf('172',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['171','172','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('178',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['93'])).

thf('185',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('186',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('187',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('188',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
   <= ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['93'])).

thf('189',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('190',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('191',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('192',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('193',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('194',plain,(
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
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('197',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['192','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['191','199'])).

thf('201',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['190','202'])).

thf('204',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['189','203'])).

thf('205',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('208',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('209',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('210',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('211',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('212',plain,(
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
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('213',plain,(
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
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('215',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('216',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['213','214','215','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['210','217'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['209','218'])).

thf('220',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['219','220'])).

thf('222',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['208','221'])).

thf('223',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['207','222'])).

thf('224',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('227',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('228',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('229',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('230',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('231',plain,(
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
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('234',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['232','233','234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['229','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['228','236'])).

thf('238',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['227','239'])).

thf('241',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['226','240'])).

thf('242',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,
    ( sk_B_2
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('245',plain,(
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

thf('246',plain,(
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
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['246','247','248'])).

thf('250',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['243','249'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['250'])).

thf('252',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['225','251'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['252'])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['206','253'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['254'])).

thf('256',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['188','255'])).

thf('257',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['256','257'])).

thf('259',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('260',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('262',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('263',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('264',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('265',plain,(
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
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('266',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['264','265'])).

thf('267',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('268',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('269',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['266','267','268'])).

thf('270',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['263','269'])).

thf('271',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['262','270'])).

thf('272',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['271','272'])).

thf('274',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['261','273'])).

thf('275',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['260','274'])).

thf('276',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['275'])).

thf('277',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['187','276'])).

thf('278',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['277','278'])).

thf('280',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['279','280'])).

thf('282',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['281','282'])).

thf('284',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['186','283'])).

thf('285',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['185','284'])).

thf('286',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['285','286'])).

thf('288',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['164','169'])).

thf('289',plain,
    ( ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['287','288'])).

thf('290',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,
    ( ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['289','290','291'])).

thf('293',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['292','293'])).

thf('295',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('296',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['294','295'])).

thf('297',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['296','297','298'])).

thf('300',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1 )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['299','300'])).

thf('302',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','183','184','301'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lc6914mXMf
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:52 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 246 iterations in 0.147s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.41/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.61  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.41/0.61  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.41/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.41/0.61  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.41/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.61  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.41/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.61  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.41/0.61  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.41/0.61  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.41/0.61  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.41/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.61  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.41/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.61  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.41/0.61  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 0.41/0.61  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.41/0.61  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.41/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.61  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.41/0.61  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.41/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.61  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.41/0.61  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.41/0.61  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.41/0.61  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.61  thf(t17_yellow19, conjecture,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.41/0.61             ( v1_subset_1 @
% 0.41/0.61               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.41/0.61             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.41/0.61             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.41/0.61             ( m1_subset_1 @
% 0.41/0.61               B @ 
% 0.41/0.61               ( k1_zfmisc_1 @
% 0.41/0.61                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.61               ( ( r3_waybel_9 @
% 0.41/0.61                   A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.41/0.61                 ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i]:
% 0.41/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.61            ( l1_pre_topc @ A ) ) =>
% 0.41/0.61          ( ![B:$i]:
% 0.41/0.61            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.41/0.61                ( v1_subset_1 @
% 0.41/0.61                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.41/0.61                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.41/0.61                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.41/0.61                ( m1_subset_1 @
% 0.41/0.61                  B @ 
% 0.41/0.61                  ( k1_zfmisc_1 @
% 0.41/0.61                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.41/0.61              ( ![C:$i]:
% 0.41/0.61                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.61                  ( ( r3_waybel_9 @
% 0.41/0.61                      A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.41/0.61                    ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t17_yellow19])).
% 0.41/0.61  thf('0', plain,
% 0.41/0.61      ((~ (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)
% 0.41/0.61        | ~ (r3_waybel_9 @ sk_A @ 
% 0.41/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('1', plain,
% 0.41/0.61      (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) | 
% 0.41/0.61       ~
% 0.41/0.61       ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf(dt_l1_pre_topc, axiom,
% 0.41/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.41/0.61  thf('2', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('3', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf(dt_k2_subset_1, axiom,
% 0.41/0.61    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.41/0.61  thf('4', plain,
% 0.41/0.61      (![X10 : $i]: (m1_subset_1 @ (k2_subset_1 @ X10) @ (k1_zfmisc_1 @ X10))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.41/0.61  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.41/0.61  thf('5', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.41/0.61      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.41/0.61  thf('6', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.41/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.61  thf('7', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf(d3_struct_0, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.41/0.61  thf('8', plain,
% 0.41/0.61      (![X14 : $i]:
% 0.41/0.61         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_B_2 @ 
% 0.41/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(d2_yellow_1, axiom,
% 0.41/0.61    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('11', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_B_2 @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.41/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.41/0.61  thf(t3_subset, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      (![X11 : $i, X12 : $i]:
% 0.41/0.61         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      ((r1_tarski @ sk_B_2 @ 
% 0.41/0.61        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.61  thf('14', plain,
% 0.41/0.61      (((r1_tarski @ sk_B_2 @ 
% 0.41/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.41/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.61      inference('sup+', [status(thm)], ['8', '13'])).
% 0.41/0.61  thf('15', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | (r1_tarski @ sk_B_2 @ 
% 0.41/0.61           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['7', '14'])).
% 0.41/0.61  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('17', plain,
% 0.41/0.61      ((r1_tarski @ sk_B_2 @ 
% 0.41/0.61        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.41/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.41/0.61  thf('18', plain,
% 0.41/0.61      (![X11 : $i, X13 : $i]:
% 0.41/0.61         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.41/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.61  thf('19', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_B_2 @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.61  thf(fc5_yellow19, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.41/0.61         ( ~( v1_xboole_0 @ B ) ) & 
% 0.41/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.41/0.61         ( ~( v1_xboole_0 @ C ) ) & 
% 0.41/0.61         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.41/0.61         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.41/0.61         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.41/0.61         ( m1_subset_1 @
% 0.41/0.61           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.41/0.61       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.41/0.61         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.41/0.61         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.41/0.61  thf('20', plain,
% 0.41/0.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.41/0.61          | (v1_xboole_0 @ X24)
% 0.41/0.61          | ~ (l1_struct_0 @ X25)
% 0.41/0.61          | (v2_struct_0 @ X25)
% 0.41/0.61          | (v1_xboole_0 @ X26)
% 0.41/0.61          | ~ (v1_subset_1 @ X26 @ (u1_struct_0 @ (k3_yellow_1 @ X24)))
% 0.41/0.61          | ~ (v2_waybel_0 @ X26 @ (k3_yellow_1 @ X24))
% 0.41/0.61          | ~ (v13_waybel_0 @ X26 @ (k3_yellow_1 @ X24))
% 0.41/0.61          | ~ (m1_subset_1 @ X26 @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X24))))
% 0.41/0.61          | (v7_waybel_0 @ (k3_yellow19 @ X25 @ X24 @ X26)))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.41/0.61  thf('21', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('22', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('23', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('24', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('25', plain,
% 0.41/0.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.41/0.61          | (v1_xboole_0 @ X24)
% 0.41/0.61          | ~ (l1_struct_0 @ X25)
% 0.41/0.61          | (v2_struct_0 @ X25)
% 0.41/0.61          | (v1_xboole_0 @ X26)
% 0.41/0.61          | ~ (v1_subset_1 @ X26 @ 
% 0.41/0.61               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X24))))
% 0.41/0.61          | ~ (v2_waybel_0 @ X26 @ (k3_lattice3 @ (k1_lattice3 @ X24)))
% 0.41/0.61          | ~ (v13_waybel_0 @ X26 @ (k3_lattice3 @ (k1_lattice3 @ X24)))
% 0.41/0.61          | ~ (m1_subset_1 @ X26 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X24)))))
% 0.41/0.61          | (v7_waybel_0 @ (k3_yellow19 @ X25 @ X24 @ X26)))),
% 0.41/0.61      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.41/0.61  thf('26', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61          | ~ (v1_subset_1 @ sk_B_2 @ 
% 0.41/0.61               (u1_struct_0 @ 
% 0.41/0.61                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['19', '25'])).
% 0.41/0.61  thf('27', plain,
% 0.41/0.61      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('28', plain,
% 0.41/0.61      (![X14 : $i]:
% 0.41/0.61         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.61  thf('29', plain,
% 0.41/0.61      ((v13_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('30', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('31', plain,
% 0.41/0.61      ((v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.61  thf('32', plain,
% 0.41/0.61      (((v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.61      inference('sup+', [status(thm)], ['28', '31'])).
% 0.41/0.61  thf('33', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | (v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['27', '32'])).
% 0.41/0.61  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('35', plain,
% 0.41/0.61      ((v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['33', '34'])).
% 0.41/0.61  thf('36', plain,
% 0.41/0.61      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('37', plain,
% 0.41/0.61      (![X14 : $i]:
% 0.41/0.61         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.61  thf('38', plain,
% 0.41/0.61      ((v2_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('39', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('40', plain,
% 0.41/0.61      ((v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.41/0.61  thf('41', plain,
% 0.41/0.61      (((v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.61      inference('sup+', [status(thm)], ['37', '40'])).
% 0.41/0.61  thf('42', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | (v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['36', '41'])).
% 0.41/0.61  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('44', plain,
% 0.41/0.61      ((v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['42', '43'])).
% 0.41/0.61  thf('45', plain,
% 0.41/0.61      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('46', plain,
% 0.41/0.61      (![X14 : $i]:
% 0.41/0.61         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.61  thf('47', plain,
% 0.41/0.61      ((v1_subset_1 @ sk_B_2 @ 
% 0.41/0.61        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('48', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('49', plain,
% 0.41/0.61      ((v1_subset_1 @ sk_B_2 @ 
% 0.41/0.61        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.41/0.61      inference('demod', [status(thm)], ['47', '48'])).
% 0.41/0.61  thf('50', plain,
% 0.41/0.61      (((v1_subset_1 @ sk_B_2 @ 
% 0.41/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.41/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.61      inference('sup+', [status(thm)], ['46', '49'])).
% 0.41/0.61  thf('51', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | (v1_subset_1 @ sk_B_2 @ 
% 0.41/0.61           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['45', '50'])).
% 0.41/0.61  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('53', plain,
% 0.41/0.61      ((v1_subset_1 @ sk_B_2 @ 
% 0.41/0.61        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.41/0.61      inference('demod', [status(thm)], ['51', '52'])).
% 0.41/0.61  thf('54', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['26', '35', '44', '53'])).
% 0.41/0.61  thf('55', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['6', '54'])).
% 0.41/0.61  thf('56', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['3', '55'])).
% 0.41/0.61  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('58', plain,
% 0.41/0.61      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('demod', [status(thm)], ['56', '57'])).
% 0.41/0.61  thf('59', plain,
% 0.41/0.61      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('60', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.41/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.61  thf('61', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_B_2 @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.61  thf(fc4_yellow19, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.41/0.61         ( ~( v1_xboole_0 @ B ) ) & 
% 0.41/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.41/0.61         ( ~( v1_xboole_0 @ C ) ) & 
% 0.41/0.61         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.41/0.61         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.41/0.61         ( m1_subset_1 @
% 0.41/0.61           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.41/0.61       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.41/0.61         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.41/0.61         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.41/0.61         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.41/0.61  thf('62', plain,
% 0.41/0.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.41/0.61          | (v1_xboole_0 @ X21)
% 0.41/0.61          | ~ (l1_struct_0 @ X22)
% 0.41/0.61          | (v2_struct_0 @ X22)
% 0.41/0.61          | (v1_xboole_0 @ X23)
% 0.41/0.61          | ~ (v2_waybel_0 @ X23 @ (k3_yellow_1 @ X21))
% 0.41/0.61          | ~ (v13_waybel_0 @ X23 @ (k3_yellow_1 @ X21))
% 0.41/0.61          | ~ (m1_subset_1 @ X23 @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X21))))
% 0.41/0.61          | (v4_orders_2 @ (k3_yellow19 @ X22 @ X21 @ X23)))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.41/0.61  thf('63', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('64', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('65', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('66', plain,
% 0.41/0.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.41/0.61          | (v1_xboole_0 @ X21)
% 0.41/0.61          | ~ (l1_struct_0 @ X22)
% 0.41/0.61          | (v2_struct_0 @ X22)
% 0.41/0.61          | (v1_xboole_0 @ X23)
% 0.41/0.61          | ~ (v2_waybel_0 @ X23 @ (k3_lattice3 @ (k1_lattice3 @ X21)))
% 0.41/0.61          | ~ (v13_waybel_0 @ X23 @ (k3_lattice3 @ (k1_lattice3 @ X21)))
% 0.41/0.61          | ~ (m1_subset_1 @ X23 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X21)))))
% 0.41/0.61          | (v4_orders_2 @ (k3_yellow19 @ X22 @ X21 @ X23)))),
% 0.41/0.61      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.41/0.61  thf('67', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['61', '66'])).
% 0.41/0.61  thf('68', plain,
% 0.41/0.61      ((v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['33', '34'])).
% 0.41/0.61  thf('69', plain,
% 0.41/0.61      ((v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['42', '43'])).
% 0.41/0.61  thf('70', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.41/0.61  thf('71', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['60', '70'])).
% 0.41/0.61  thf('72', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['59', '71'])).
% 0.41/0.61  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('74', plain,
% 0.41/0.61      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('demod', [status(thm)], ['72', '73'])).
% 0.41/0.61  thf('75', plain,
% 0.41/0.61      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('76', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.41/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.61  thf('77', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_B_2 @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.61  thf(dt_k3_yellow19, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.41/0.61         ( ~( v1_xboole_0 @ B ) ) & 
% 0.41/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.41/0.61         ( ~( v1_xboole_0 @ C ) ) & 
% 0.41/0.61         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.41/0.61         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.41/0.61         ( m1_subset_1 @
% 0.41/0.61           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.41/0.61       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.41/0.61         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.41/0.61         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.41/0.61  thf('78', plain,
% 0.41/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.41/0.61          | (v1_xboole_0 @ X18)
% 0.41/0.61          | ~ (l1_struct_0 @ X19)
% 0.41/0.61          | (v2_struct_0 @ X19)
% 0.41/0.61          | (v1_xboole_0 @ X20)
% 0.41/0.61          | ~ (v2_waybel_0 @ X20 @ (k3_yellow_1 @ X18))
% 0.41/0.61          | ~ (v13_waybel_0 @ X20 @ (k3_yellow_1 @ X18))
% 0.41/0.61          | ~ (m1_subset_1 @ X20 @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X18))))
% 0.41/0.61          | (l1_waybel_0 @ (k3_yellow19 @ X19 @ X18 @ X20) @ X19))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.41/0.61  thf('79', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('80', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('81', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('82', plain,
% 0.41/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.41/0.61          | (v1_xboole_0 @ X18)
% 0.41/0.61          | ~ (l1_struct_0 @ X19)
% 0.41/0.61          | (v2_struct_0 @ X19)
% 0.41/0.61          | (v1_xboole_0 @ X20)
% 0.41/0.61          | ~ (v2_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.41/0.61          | ~ (v13_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.41/0.61          | ~ (m1_subset_1 @ X20 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18)))))
% 0.41/0.61          | (l1_waybel_0 @ (k3_yellow19 @ X19 @ X18 @ X20) @ X19))),
% 0.41/0.61      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 0.41/0.61  thf('83', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.41/0.61           X0)
% 0.41/0.61          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['77', '82'])).
% 0.41/0.61  thf('84', plain,
% 0.41/0.61      ((v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['33', '34'])).
% 0.41/0.61  thf('85', plain,
% 0.41/0.61      ((v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['42', '43'])).
% 0.41/0.61  thf('86', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.41/0.61           X0)
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.41/0.61  thf('87', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | (l1_waybel_0 @ 
% 0.41/0.61           (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['76', '86'])).
% 0.41/0.61  thf('88', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | (l1_waybel_0 @ 
% 0.41/0.61           (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['75', '87'])).
% 0.41/0.61  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('90', plain,
% 0.41/0.61      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.41/0.61         sk_A)
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('demod', [status(thm)], ['88', '89'])).
% 0.41/0.61  thf('91', plain,
% 0.41/0.61      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('92', plain,
% 0.41/0.61      (![X14 : $i]:
% 0.41/0.61         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.61  thf('93', plain,
% 0.41/0.61      (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)
% 0.41/0.61        | (r3_waybel_9 @ sk_A @ 
% 0.41/0.61           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('94', plain,
% 0.41/0.61      (((r3_waybel_9 @ sk_A @ 
% 0.41/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1))
% 0.41/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('split', [status(esa)], ['93'])).
% 0.41/0.61  thf('95', plain,
% 0.41/0.61      ((((r3_waybel_9 @ sk_A @ 
% 0.41/0.61          (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)
% 0.41/0.61         | ~ (l1_struct_0 @ sk_A)))
% 0.41/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['92', '94'])).
% 0.41/0.61  thf('96', plain,
% 0.41/0.61      (((~ (l1_pre_topc @ sk_A)
% 0.41/0.61         | (r3_waybel_9 @ sk_A @ 
% 0.41/0.61            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))
% 0.41/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['91', '95'])).
% 0.41/0.61  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('98', plain,
% 0.41/0.61      (((r3_waybel_9 @ sk_A @ 
% 0.41/0.61         (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1))
% 0.41/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('demod', [status(thm)], ['96', '97'])).
% 0.41/0.61  thf('99', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t12_yellow19, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.41/0.61             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.61               ( ( r3_waybel_9 @ A @ B @ C ) <=>
% 0.41/0.61                 ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.41/0.61  thf('100', plain,
% 0.41/0.61      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X27)
% 0.41/0.61          | ~ (v4_orders_2 @ X27)
% 0.41/0.61          | ~ (v7_waybel_0 @ X27)
% 0.41/0.61          | ~ (l1_waybel_0 @ X27 @ X28)
% 0.41/0.61          | ~ (r3_waybel_9 @ X28 @ X27 @ X29)
% 0.41/0.61          | (r1_waybel_7 @ X28 @ (k2_yellow19 @ X28 @ X27) @ X29)
% 0.41/0.61          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.41/0.61          | ~ (l1_pre_topc @ X28)
% 0.41/0.61          | ~ (v2_pre_topc @ X28)
% 0.41/0.61          | (v2_struct_0 @ X28))),
% 0.41/0.61      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.41/0.61  thf('101', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_A)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.41/0.61          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C_1)
% 0.41/0.61          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C_1)
% 0.41/0.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.41/0.61          | ~ (v7_waybel_0 @ X0)
% 0.41/0.61          | ~ (v4_orders_2 @ X0)
% 0.41/0.61          | (v2_struct_0 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['99', '100'])).
% 0.41/0.61  thf('102', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('104', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_A)
% 0.41/0.61          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C_1)
% 0.41/0.61          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C_1)
% 0.41/0.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.41/0.61          | ~ (v7_waybel_0 @ X0)
% 0.41/0.61          | ~ (v4_orders_2 @ X0)
% 0.41/0.61          | (v2_struct_0 @ X0))),
% 0.41/0.61      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.41/0.61  thf('105', plain,
% 0.41/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61         | ~ (v4_orders_2 @ 
% 0.41/0.61              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61         | ~ (v7_waybel_0 @ 
% 0.41/0.61              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61         | ~ (l1_waybel_0 @ 
% 0.41/0.61              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.41/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.41/0.61            (k2_yellow19 @ sk_A @ 
% 0.41/0.61             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2)) @ 
% 0.41/0.61            sk_C_1)
% 0.41/0.61         | (v2_struct_0 @ sk_A)))
% 0.41/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['98', '104'])).
% 0.41/0.61  thf('106', plain,
% 0.41/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.41/0.61            (k2_yellow19 @ sk_A @ 
% 0.41/0.61             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2)) @ 
% 0.41/0.61            sk_C_1)
% 0.41/0.61         | ~ (v7_waybel_0 @ 
% 0.41/0.61              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61         | ~ (v4_orders_2 @ 
% 0.41/0.61              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))))
% 0.41/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['90', '105'])).
% 0.41/0.61  thf('107', plain,
% 0.41/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61         | ~ (v4_orders_2 @ 
% 0.41/0.61              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61         | ~ (v7_waybel_0 @ 
% 0.41/0.61              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.41/0.61            (k2_yellow19 @ sk_A @ 
% 0.41/0.61             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2)) @ 
% 0.41/0.61            sk_C_1)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['106'])).
% 0.41/0.61  thf('108', plain,
% 0.41/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.41/0.61            (k2_yellow19 @ sk_A @ 
% 0.41/0.61             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2)) @ 
% 0.41/0.61            sk_C_1)
% 0.41/0.61         | ~ (v7_waybel_0 @ 
% 0.41/0.61              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))))
% 0.41/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['74', '107'])).
% 0.41/0.61  thf('109', plain,
% 0.41/0.61      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('110', plain,
% 0.41/0.61      (![X14 : $i]:
% 0.41/0.61         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.61  thf('111', plain,
% 0.41/0.61      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('112', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_B_2 @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.41/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.41/0.61  thf(t15_yellow19, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.41/0.61             ( v1_subset_1 @
% 0.41/0.61               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.41/0.61             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.41/0.61             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.41/0.61             ( m1_subset_1 @
% 0.41/0.61               B @ 
% 0.41/0.61               ( k1_zfmisc_1 @
% 0.41/0.61                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.41/0.61           ( ( B ) =
% 0.41/0.61             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.41/0.61  thf('113', plain,
% 0.41/0.61      (![X30 : $i, X31 : $i]:
% 0.41/0.61         ((v1_xboole_0 @ X30)
% 0.41/0.61          | ~ (v1_subset_1 @ X30 @ 
% 0.41/0.61               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X31))))
% 0.41/0.61          | ~ (v2_waybel_0 @ X30 @ (k3_yellow_1 @ (k2_struct_0 @ X31)))
% 0.41/0.61          | ~ (v13_waybel_0 @ X30 @ (k3_yellow_1 @ (k2_struct_0 @ X31)))
% 0.41/0.61          | ~ (m1_subset_1 @ X30 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X31)))))
% 0.41/0.61          | ((X30)
% 0.41/0.61              = (k2_yellow19 @ X31 @ 
% 0.41/0.61                 (k3_yellow19 @ X31 @ (k2_struct_0 @ X31) @ X30)))
% 0.41/0.61          | ~ (l1_struct_0 @ X31)
% 0.41/0.61          | (v2_struct_0 @ X31))),
% 0.41/0.61      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.41/0.61  thf('114', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('115', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('116', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('117', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('118', plain,
% 0.41/0.61      (![X30 : $i, X31 : $i]:
% 0.41/0.61         ((v1_xboole_0 @ X30)
% 0.41/0.61          | ~ (v1_subset_1 @ X30 @ 
% 0.41/0.61               (u1_struct_0 @ 
% 0.41/0.61                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X31)))))
% 0.41/0.61          | ~ (v2_waybel_0 @ X30 @ 
% 0.41/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X31))))
% 0.41/0.61          | ~ (v13_waybel_0 @ X30 @ 
% 0.41/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X31))))
% 0.41/0.61          | ~ (m1_subset_1 @ X30 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (u1_struct_0 @ 
% 0.41/0.61                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X31))))))
% 0.41/0.61          | ((X30)
% 0.41/0.61              = (k2_yellow19 @ X31 @ 
% 0.41/0.61                 (k3_yellow19 @ X31 @ (k2_struct_0 @ X31) @ X30)))
% 0.41/0.61          | ~ (l1_struct_0 @ X31)
% 0.41/0.61          | (v2_struct_0 @ X31))),
% 0.41/0.61      inference('demod', [status(thm)], ['113', '114', '115', '116', '117'])).
% 0.41/0.61  thf('119', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_A)
% 0.41/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.41/0.61        | ((sk_B_2)
% 0.41/0.61            = (k2_yellow19 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.41/0.61        | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.41/0.61        | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.41/0.61        | ~ (v1_subset_1 @ sk_B_2 @ 
% 0.41/0.61             (u1_struct_0 @ 
% 0.41/0.61              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2))),
% 0.41/0.61      inference('sup-', [status(thm)], ['112', '118'])).
% 0.41/0.61  thf('120', plain,
% 0.41/0.61      ((v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.61  thf('121', plain,
% 0.41/0.61      ((v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.41/0.61  thf('122', plain,
% 0.41/0.61      ((v1_subset_1 @ sk_B_2 @ 
% 0.41/0.61        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.41/0.61      inference('demod', [status(thm)], ['47', '48'])).
% 0.41/0.61  thf('123', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_A)
% 0.41/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.41/0.61        | ((sk_B_2)
% 0.41/0.61            = (k2_yellow19 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2))),
% 0.41/0.61      inference('demod', [status(thm)], ['119', '120', '121', '122'])).
% 0.41/0.61  thf('124', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | ((sk_B_2)
% 0.41/0.61            = (k2_yellow19 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.41/0.61        | (v2_struct_0 @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['111', '123'])).
% 0.41/0.61  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('126', plain,
% 0.41/0.61      (((v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | ((sk_B_2)
% 0.41/0.61            = (k2_yellow19 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.41/0.61        | (v2_struct_0 @ sk_A))),
% 0.41/0.61      inference('demod', [status(thm)], ['124', '125'])).
% 0.41/0.61  thf('127', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('128', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_A)
% 0.41/0.61        | ((sk_B_2)
% 0.41/0.61            = (k2_yellow19 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))),
% 0.41/0.61      inference('clc', [status(thm)], ['126', '127'])).
% 0.41/0.61  thf('129', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('130', plain,
% 0.41/0.61      (((sk_B_2)
% 0.41/0.61         = (k2_yellow19 @ sk_A @ 
% 0.41/0.61            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.41/0.61      inference('clc', [status(thm)], ['128', '129'])).
% 0.41/0.61  thf('131', plain,
% 0.41/0.61      ((((sk_B_2)
% 0.41/0.61          = (k2_yellow19 @ sk_A @ 
% 0.41/0.61             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2)))
% 0.41/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.61      inference('sup+', [status(thm)], ['110', '130'])).
% 0.41/0.61  thf('132', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | ((sk_B_2)
% 0.41/0.61            = (k2_yellow19 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['109', '131'])).
% 0.41/0.61  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('134', plain,
% 0.41/0.61      (((sk_B_2)
% 0.41/0.61         = (k2_yellow19 @ sk_A @ 
% 0.41/0.61            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2)))),
% 0.41/0.61      inference('demod', [status(thm)], ['132', '133'])).
% 0.41/0.61  thf('135', plain,
% 0.41/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)
% 0.41/0.61         | ~ (v7_waybel_0 @ 
% 0.41/0.61              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))))
% 0.41/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('demod', [status(thm)], ['108', '134'])).
% 0.41/0.61  thf('136', plain,
% 0.41/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61         | ~ (v7_waybel_0 @ 
% 0.41/0.61              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['135'])).
% 0.41/0.61  thf('137', plain,
% 0.41/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)
% 0.41/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))))
% 0.41/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['58', '136'])).
% 0.41/0.61  thf('138', plain,
% 0.41/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['137'])).
% 0.41/0.61  thf('139', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.41/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.61  thf('140', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_B_2 @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.61  thf('141', plain,
% 0.41/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.41/0.61          | (v1_xboole_0 @ X18)
% 0.41/0.61          | ~ (l1_struct_0 @ X19)
% 0.41/0.61          | (v2_struct_0 @ X19)
% 0.41/0.61          | (v1_xboole_0 @ X20)
% 0.41/0.61          | ~ (v2_waybel_0 @ X20 @ (k3_yellow_1 @ X18))
% 0.41/0.61          | ~ (v13_waybel_0 @ X20 @ (k3_yellow_1 @ X18))
% 0.41/0.61          | ~ (m1_subset_1 @ X20 @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X18))))
% 0.41/0.61          | ~ (v2_struct_0 @ (k3_yellow19 @ X19 @ X18 @ X20)))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.41/0.61  thf('142', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('143', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('144', plain,
% 0.41/0.61      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.61  thf('145', plain,
% 0.41/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.41/0.61          | (v1_xboole_0 @ X18)
% 0.41/0.61          | ~ (l1_struct_0 @ X19)
% 0.41/0.61          | (v2_struct_0 @ X19)
% 0.41/0.61          | (v1_xboole_0 @ X20)
% 0.41/0.61          | ~ (v2_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.41/0.61          | ~ (v13_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.41/0.61          | ~ (m1_subset_1 @ X20 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18)))))
% 0.41/0.61          | ~ (v2_struct_0 @ (k3_yellow19 @ X19 @ X18 @ X20)))),
% 0.41/0.61      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 0.41/0.61  thf('146', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['140', '145'])).
% 0.41/0.61  thf('147', plain,
% 0.41/0.61      ((v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['33', '34'])).
% 0.41/0.61  thf('148', plain,
% 0.41/0.61      ((v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['42', '43'])).
% 0.41/0.61  thf('149', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['146', '147', '148'])).
% 0.41/0.61  thf('150', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_2)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['139', '149'])).
% 0.41/0.61  thf('151', plain,
% 0.41/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | ~ (l1_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['138', '150'])).
% 0.41/0.61  thf('152', plain,
% 0.41/0.61      (((~ (l1_struct_0 @ sk_A)
% 0.41/0.61         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['151'])).
% 0.41/0.61  thf('153', plain,
% 0.41/0.61      (((~ (l1_pre_topc @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))
% 0.41/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['2', '152'])).
% 0.41/0.61  thf('154', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('155', plain,
% 0.41/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))
% 0.41/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('demod', [status(thm)], ['153', '154'])).
% 0.41/0.61  thf('156', plain,
% 0.41/0.61      ((~ (r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1))
% 0.41/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('157', plain,
% 0.41/0.61      ((((v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) & 
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['155', '156'])).
% 0.41/0.61  thf('158', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('159', plain,
% 0.41/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.41/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) & 
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('clc', [status(thm)], ['157', '158'])).
% 0.41/0.61  thf('160', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('161', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.41/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) & 
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('clc', [status(thm)], ['159', '160'])).
% 0.41/0.61  thf(rc7_pre_topc, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ?[B:$i]:
% 0.41/0.61         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.41/0.61           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.41/0.61  thf('162', plain,
% 0.41/0.61      (![X16 : $i]:
% 0.41/0.61         ((m1_subset_1 @ (sk_B_1 @ X16) @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.41/0.61          | ~ (l1_pre_topc @ X16)
% 0.41/0.61          | ~ (v2_pre_topc @ X16)
% 0.41/0.61          | (v2_struct_0 @ X16))),
% 0.41/0.61      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.41/0.61  thf('163', plain,
% 0.41/0.61      (![X11 : $i, X12 : $i]:
% 0.41/0.61         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.61  thf('164', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | (r1_tarski @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['162', '163'])).
% 0.41/0.61  thf(t3_xboole_0, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.41/0.61            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.41/0.61       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.41/0.61            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.41/0.61  thf('165', plain,
% 0.41/0.61      (![X3 : $i, X4 : $i]:
% 0.41/0.61         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.41/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.41/0.61  thf(d1_xboole_0, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.61  thf('166', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.61  thf('167', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['165', '166'])).
% 0.41/0.61  thf(t69_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.41/0.61       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.41/0.61  thf('168', plain,
% 0.41/0.61      (![X7 : $i, X8 : $i]:
% 0.41/0.61         (~ (r1_xboole_0 @ X7 @ X8)
% 0.41/0.61          | ~ (r1_tarski @ X7 @ X8)
% 0.41/0.61          | (v1_xboole_0 @ X7))),
% 0.41/0.61      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.41/0.61  thf('169', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ X1) | ~ (r1_tarski @ X1 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['167', '168'])).
% 0.41/0.61  thf('170', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.41/0.61          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['164', '169'])).
% 0.41/0.61  thf('171', plain,
% 0.41/0.61      ((((v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | ~ (v2_pre_topc @ sk_A)
% 0.41/0.61         | ~ (l1_pre_topc @ sk_A)))
% 0.41/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) & 
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['161', '170'])).
% 0.41/0.61  thf('172', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('173', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('174', plain,
% 0.41/0.61      ((((v1_xboole_0 @ (sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.41/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) & 
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('demod', [status(thm)], ['171', '172', '173'])).
% 0.41/0.61  thf('175', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('176', plain,
% 0.41/0.61      (((v1_xboole_0 @ (sk_B_1 @ sk_A)))
% 0.41/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) & 
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('clc', [status(thm)], ['174', '175'])).
% 0.41/0.61  thf('177', plain,
% 0.41/0.61      (![X16 : $i]:
% 0.41/0.61         (~ (v1_xboole_0 @ (sk_B_1 @ X16))
% 0.41/0.61          | ~ (l1_pre_topc @ X16)
% 0.41/0.61          | ~ (v2_pre_topc @ X16)
% 0.41/0.61          | (v2_struct_0 @ X16))),
% 0.41/0.61      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.41/0.61  thf('178', plain,
% 0.41/0.61      ((((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.41/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) & 
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['176', '177'])).
% 0.41/0.61  thf('179', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('180', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('181', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_A))
% 0.41/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) & 
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('demod', [status(thm)], ['178', '179', '180'])).
% 0.41/0.61  thf('182', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('183', plain,
% 0.41/0.61      (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) | 
% 0.41/0.61       ~
% 0.41/0.61       ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['181', '182'])).
% 0.41/0.61  thf('184', plain,
% 0.41/0.61      (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) | 
% 0.41/0.61       ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1))),
% 0.41/0.61      inference('split', [status(esa)], ['93'])).
% 0.41/0.61  thf('185', plain,
% 0.41/0.61      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('186', plain,
% 0.41/0.61      (![X14 : $i]:
% 0.41/0.61         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.61  thf('187', plain,
% 0.41/0.61      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('188', plain,
% 0.41/0.61      (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1))
% 0.41/0.61         <= (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 0.41/0.61      inference('split', [status(esa)], ['93'])).
% 0.41/0.61  thf('189', plain,
% 0.41/0.61      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('190', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.41/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.61  thf('191', plain,
% 0.41/0.61      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('192', plain,
% 0.41/0.61      (![X14 : $i]:
% 0.41/0.61         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.61  thf('193', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_B_2 @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.41/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.41/0.61  thf('194', plain,
% 0.41/0.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.41/0.61          | (v1_xboole_0 @ X21)
% 0.41/0.61          | ~ (l1_struct_0 @ X22)
% 0.41/0.61          | (v2_struct_0 @ X22)
% 0.41/0.61          | (v1_xboole_0 @ X23)
% 0.41/0.61          | ~ (v2_waybel_0 @ X23 @ (k3_lattice3 @ (k1_lattice3 @ X21)))
% 0.41/0.61          | ~ (v13_waybel_0 @ X23 @ (k3_lattice3 @ (k1_lattice3 @ X21)))
% 0.41/0.61          | ~ (m1_subset_1 @ X23 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X21)))))
% 0.41/0.61          | (v4_orders_2 @ (k3_yellow19 @ X22 @ X21 @ X23)))),
% 0.41/0.61      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.41/0.61  thf('195', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.41/0.61          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['193', '194'])).
% 0.41/0.61  thf('196', plain,
% 0.41/0.61      ((v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.61  thf('197', plain,
% 0.41/0.61      ((v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.41/0.61  thf('198', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['195', '196', '197'])).
% 0.41/0.61  thf('199', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.41/0.61          | ~ (l1_struct_0 @ sk_A)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['192', '198'])).
% 0.41/0.61  thf('200', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ sk_A)
% 0.41/0.61          | (v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['191', '199'])).
% 0.41/0.61  thf('201', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('202', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['200', '201'])).
% 0.41/0.61  thf('203', plain,
% 0.41/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['190', '202'])).
% 0.41/0.61  thf('204', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['189', '203'])).
% 0.41/0.61  thf('205', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('206', plain,
% 0.41/0.61      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.41/0.61      inference('demod', [status(thm)], ['204', '205'])).
% 0.41/0.61  thf('207', plain,
% 0.41/0.61      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('208', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.41/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.61  thf('209', plain,
% 0.41/0.61      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('210', plain,
% 0.41/0.61      (![X14 : $i]:
% 0.41/0.61         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.61  thf('211', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_B_2 @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.41/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.41/0.61  thf('212', plain,
% 0.41/0.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.41/0.61          | (v1_xboole_0 @ X24)
% 0.41/0.61          | ~ (l1_struct_0 @ X25)
% 0.41/0.61          | (v2_struct_0 @ X25)
% 0.41/0.61          | (v1_xboole_0 @ X26)
% 0.41/0.61          | ~ (v1_subset_1 @ X26 @ 
% 0.41/0.61               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X24))))
% 0.41/0.61          | ~ (v2_waybel_0 @ X26 @ (k3_lattice3 @ (k1_lattice3 @ X24)))
% 0.41/0.61          | ~ (v13_waybel_0 @ X26 @ (k3_lattice3 @ (k1_lattice3 @ X24)))
% 0.41/0.61          | ~ (m1_subset_1 @ X26 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X24)))))
% 0.41/0.61          | (v7_waybel_0 @ (k3_yellow19 @ X25 @ X24 @ X26)))),
% 0.41/0.61      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.41/0.61  thf('213', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.41/0.61          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.41/0.61          | ~ (v1_subset_1 @ sk_B_2 @ 
% 0.41/0.61               (u1_struct_0 @ 
% 0.41/0.61                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['211', '212'])).
% 0.41/0.61  thf('214', plain,
% 0.41/0.61      ((v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.61  thf('215', plain,
% 0.41/0.61      ((v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.41/0.61  thf('216', plain,
% 0.41/0.61      ((v1_subset_1 @ sk_B_2 @ 
% 0.41/0.61        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.41/0.61      inference('demod', [status(thm)], ['47', '48'])).
% 0.41/0.61  thf('217', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['213', '214', '215', '216'])).
% 0.41/0.61  thf('218', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.41/0.61          | ~ (l1_struct_0 @ sk_A)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['210', '217'])).
% 0.41/0.61  thf('219', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ sk_A)
% 0.41/0.61          | (v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['209', '218'])).
% 0.41/0.61  thf('220', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('221', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['219', '220'])).
% 0.41/0.61  thf('222', plain,
% 0.41/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['208', '221'])).
% 0.41/0.61  thf('223', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['207', '222'])).
% 0.41/0.61  thf('224', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('225', plain,
% 0.41/0.61      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.41/0.61      inference('demod', [status(thm)], ['223', '224'])).
% 0.41/0.61  thf('226', plain,
% 0.41/0.61      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('227', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.41/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.61  thf('228', plain,
% 0.41/0.61      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('229', plain,
% 0.41/0.61      (![X14 : $i]:
% 0.41/0.61         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.61  thf('230', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_B_2 @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.41/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.41/0.61  thf('231', plain,
% 0.41/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.41/0.61          | (v1_xboole_0 @ X18)
% 0.41/0.61          | ~ (l1_struct_0 @ X19)
% 0.41/0.61          | (v2_struct_0 @ X19)
% 0.41/0.61          | (v1_xboole_0 @ X20)
% 0.41/0.61          | ~ (v2_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.41/0.61          | ~ (v13_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.41/0.61          | ~ (m1_subset_1 @ X20 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18)))))
% 0.41/0.61          | (l1_waybel_0 @ (k3_yellow19 @ X19 @ X18 @ X20) @ X19))),
% 0.41/0.61      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 0.41/0.61  thf('232', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.41/0.61           X0)
% 0.41/0.61          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.41/0.61          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['230', '231'])).
% 0.41/0.61  thf('233', plain,
% 0.41/0.61      ((v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.61  thf('234', plain,
% 0.41/0.61      ((v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.41/0.61  thf('235', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.41/0.61           X0)
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['232', '233', '234'])).
% 0.41/0.61  thf('236', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.41/0.61          | ~ (l1_struct_0 @ sk_A)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (l1_waybel_0 @ 
% 0.41/0.61             (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['229', '235'])).
% 0.41/0.61  thf('237', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ sk_A)
% 0.41/0.61          | (l1_waybel_0 @ 
% 0.41/0.61             (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['228', '236'])).
% 0.41/0.61  thf('238', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('239', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.41/0.61           X0)
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['237', '238'])).
% 0.41/0.61  thf('240', plain,
% 0.41/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | (l1_waybel_0 @ 
% 0.41/0.61           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['227', '239'])).
% 0.41/0.61  thf('241', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | (l1_waybel_0 @ 
% 0.41/0.61           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['226', '240'])).
% 0.41/0.61  thf('242', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('243', plain,
% 0.41/0.61      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.41/0.61         sk_A)
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.41/0.61      inference('demod', [status(thm)], ['241', '242'])).
% 0.41/0.61  thf('244', plain,
% 0.41/0.61      (((sk_B_2)
% 0.41/0.61         = (k2_yellow19 @ sk_A @ 
% 0.41/0.61            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.41/0.61      inference('clc', [status(thm)], ['128', '129'])).
% 0.41/0.61  thf('245', plain,
% 0.41/0.61      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X27)
% 0.41/0.61          | ~ (v4_orders_2 @ X27)
% 0.41/0.61          | ~ (v7_waybel_0 @ X27)
% 0.41/0.61          | ~ (l1_waybel_0 @ X27 @ X28)
% 0.41/0.61          | ~ (r1_waybel_7 @ X28 @ (k2_yellow19 @ X28 @ X27) @ X29)
% 0.41/0.61          | (r3_waybel_9 @ X28 @ X27 @ X29)
% 0.41/0.61          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.41/0.61          | ~ (l1_pre_topc @ X28)
% 0.41/0.61          | ~ (v2_pre_topc @ X28)
% 0.41/0.61          | (v2_struct_0 @ X28))),
% 0.41/0.61      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.41/0.61  thf('246', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 0.41/0.61          | (v2_struct_0 @ sk_A)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.41/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 0.41/0.61          | ~ (l1_waybel_0 @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.41/0.61          | ~ (v7_waybel_0 @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | ~ (v4_orders_2 @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['244', '245'])).
% 0.41/0.61  thf('247', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('248', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('249', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 0.41/0.61          | (v2_struct_0 @ sk_A)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.41/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 0.41/0.61          | ~ (l1_waybel_0 @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.41/0.61          | ~ (v7_waybel_0 @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | ~ (v4_orders_2 @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.41/0.61      inference('demod', [status(thm)], ['246', '247', '248'])).
% 0.41/0.61  thf('250', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | (v2_struct_0 @ sk_A)
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | ~ (v4_orders_2 @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | ~ (v7_waybel_0 @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.41/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | (v2_struct_0 @ sk_A)
% 0.41/0.61          | ~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['243', '249'])).
% 0.41/0.61  thf('251', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.41/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 0.41/0.61          | ~ (v7_waybel_0 @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | ~ (v4_orders_2 @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ sk_A)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['250'])).
% 0.41/0.61  thf('252', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | (v2_struct_0 @ sk_A)
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | (v2_struct_0 @ sk_A)
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | ~ (v4_orders_2 @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.41/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | ~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['225', '251'])).
% 0.41/0.61  thf('253', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.41/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 0.41/0.61          | ~ (v4_orders_2 @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ sk_A)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['252'])).
% 0.41/0.61  thf('254', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | (v2_struct_0 @ sk_A)
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | (v2_struct_0 @ sk_A)
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.41/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | ~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['206', '253'])).
% 0.41/0.61  thf('255', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (r1_waybel_7 @ sk_A @ sk_B_2 @ X0)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.41/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ X0)
% 0.41/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ sk_A)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['254'])).
% 0.41/0.61  thf('256', plain,
% 0.41/0.61      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61         | (r3_waybel_9 @ sk_A @ 
% 0.41/0.61            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)
% 0.41/0.61         | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61         <= (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['188', '255'])).
% 0.41/0.61  thf('257', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('258', plain,
% 0.41/0.61      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61         | (r3_waybel_9 @ sk_A @ 
% 0.41/0.61            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))
% 0.41/0.61         <= (((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 0.41/0.61      inference('demod', [status(thm)], ['256', '257'])).
% 0.41/0.61  thf('259', plain,
% 0.41/0.61      ((~ (r3_waybel_9 @ sk_A @ 
% 0.41/0.61           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('260', plain,
% 0.41/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 0.41/0.61             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['258', '259'])).
% 0.41/0.61  thf('261', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.41/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.61  thf('262', plain,
% 0.41/0.61      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('263', plain,
% 0.41/0.61      (![X14 : $i]:
% 0.41/0.61         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.61  thf('264', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_B_2 @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.41/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.41/0.61  thf('265', plain,
% 0.41/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.41/0.61          | (v1_xboole_0 @ X18)
% 0.41/0.61          | ~ (l1_struct_0 @ X19)
% 0.41/0.61          | (v2_struct_0 @ X19)
% 0.41/0.61          | (v1_xboole_0 @ X20)
% 0.41/0.61          | ~ (v2_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.41/0.61          | ~ (v13_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.41/0.61          | ~ (m1_subset_1 @ X20 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18)))))
% 0.41/0.61          | ~ (v2_struct_0 @ (k3_yellow19 @ X19 @ X18 @ X20)))),
% 0.41/0.61      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 0.41/0.61  thf('266', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.41/0.61          | ~ (v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['264', '265'])).
% 0.41/0.61  thf('267', plain,
% 0.41/0.61      ((v13_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.61  thf('268', plain,
% 0.41/0.61      ((v2_waybel_0 @ sk_B_2 @ 
% 0.41/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.41/0.61  thf('269', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['266', '267', '268'])).
% 0.41/0.61  thf('270', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.41/0.61          | ~ (l1_struct_0 @ sk_A)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['263', '269'])).
% 0.41/0.61  thf('271', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ sk_A)
% 0.41/0.61          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['262', '270'])).
% 0.41/0.61  thf('272', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('273', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_2))
% 0.41/0.61          | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | ~ (l1_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['271', '272'])).
% 0.41/0.61  thf('274', plain,
% 0.41/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.41/0.61        | (v2_struct_0 @ sk_A)
% 0.41/0.61        | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['261', '273'])).
% 0.41/0.61  thf('275', plain,
% 0.41/0.61      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | ~ (l1_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 0.41/0.61             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['260', '274'])).
% 0.41/0.61  thf('276', plain,
% 0.41/0.61      (((~ (l1_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 0.41/0.61             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['275'])).
% 0.41/0.61  thf('277', plain,
% 0.41/0.61      (((~ (l1_pre_topc @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 0.41/0.61             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['187', '276'])).
% 0.41/0.61  thf('278', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('279', plain,
% 0.41/0.61      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | (v1_xboole_0 @ sk_B_2)))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 0.41/0.61             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 0.41/0.61      inference('demod', [status(thm)], ['277', '278'])).
% 0.41/0.61  thf('280', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('281', plain,
% 0.41/0.61      ((((v1_xboole_0 @ sk_B_2) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 0.41/0.61             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 0.41/0.61      inference('clc', [status(thm)], ['279', '280'])).
% 0.41/0.61  thf('282', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('283', plain,
% 0.41/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 0.41/0.61             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 0.41/0.61      inference('clc', [status(thm)], ['281', '282'])).
% 0.41/0.61  thf('284', plain,
% 0.41/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 0.41/0.61             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['186', '283'])).
% 0.41/0.61  thf('285', plain,
% 0.41/0.61      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 0.41/0.61             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['185', '284'])).
% 0.41/0.61  thf('286', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('287', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 0.41/0.61             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 0.41/0.61      inference('demod', [status(thm)], ['285', '286'])).
% 0.41/0.61  thf('288', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0)
% 0.41/0.61          | (v2_struct_0 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.41/0.61          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['164', '169'])).
% 0.41/0.61  thf('289', plain,
% 0.41/0.61      ((((v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.41/0.61         | (v2_struct_0 @ sk_A)
% 0.41/0.61         | ~ (v2_pre_topc @ sk_A)
% 0.41/0.61         | ~ (l1_pre_topc @ sk_A)))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 0.41/0.61             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['287', '288'])).
% 0.41/0.61  thf('290', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('291', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('292', plain,
% 0.41/0.61      ((((v1_xboole_0 @ (sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 0.41/0.61             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 0.41/0.61      inference('demod', [status(thm)], ['289', '290', '291'])).
% 0.41/0.61  thf('293', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('294', plain,
% 0.41/0.61      (((v1_xboole_0 @ (sk_B_1 @ sk_A)))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 0.41/0.61             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 0.41/0.61      inference('clc', [status(thm)], ['292', '293'])).
% 0.41/0.61  thf('295', plain,
% 0.41/0.61      (![X16 : $i]:
% 0.41/0.61         (~ (v1_xboole_0 @ (sk_B_1 @ X16))
% 0.41/0.61          | ~ (l1_pre_topc @ X16)
% 0.41/0.61          | ~ (v2_pre_topc @ X16)
% 0.41/0.61          | (v2_struct_0 @ X16))),
% 0.41/0.61      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.41/0.61  thf('296', plain,
% 0.41/0.61      ((((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 0.41/0.61             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['294', '295'])).
% 0.41/0.61  thf('297', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('298', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('299', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_A))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1)) & 
% 0.41/0.61             ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 0.41/0.61      inference('demod', [status(thm)], ['296', '297', '298'])).
% 0.41/0.61  thf('300', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('301', plain,
% 0.41/0.61      (~ ((r1_waybel_7 @ sk_A @ sk_B_2 @ sk_C_1)) | 
% 0.41/0.61       ((r3_waybel_9 @ sk_A @ 
% 0.41/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2) @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['299', '300'])).
% 0.41/0.61  thf('302', plain, ($false),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['1', '183', '184', '301'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
