%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VDniEMmHUT

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:52 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  281 ( 897 expanded)
%              Number of leaves         :   41 ( 293 expanded)
%              Depth                    :   42
%              Number of atoms          : 3789 (16217 expanded)
%              Number of equality atoms :   49 ( 233 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

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
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('10',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('12',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

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

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v2_waybel_0 @ X15 @ ( k3_yellow_1 @ X13 ) )
      | ~ ( v13_waybel_0 @ X15 @ ( k3_yellow_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X13 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('19',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('20',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('21',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v2_waybel_0 @ X15 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) )
      | ~ ( v13_waybel_0 @ X15 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X14 @ X13 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('25',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('26',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('28',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('37',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['23','32','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','42'])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

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

thf('50',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_xboole_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( v1_subset_1 @ X18 @ ( u1_struct_0 @ ( k3_yellow_1 @ X16 ) ) )
      | ~ ( v2_waybel_0 @ X18 @ ( k3_yellow_1 @ X16 ) )
      | ~ ( v13_waybel_0 @ X18 @ ( k3_yellow_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X16 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X17 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('51',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('52',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('53',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('54',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('55',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v1_xboole_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( v1_subset_1 @ X18 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) )
      | ~ ( v2_waybel_0 @ X18 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) )
      | ~ ( v13_waybel_0 @ X18 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X17 @ X16 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('58',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('59',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('63',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['56','57','58','67'])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','68'])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('74',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

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

thf('76',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ X10 ) )
      | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X10 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X11 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('77',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('78',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('79',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('80',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v2_waybel_0 @ X12 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) )
      | ~ ( v13_waybel_0 @ X12 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X11 @ X10 @ X12 ) @ X11 ) ) ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('83',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['74','84'])).

thf('86',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('90',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['91'])).

thf('93',plain,
    ( ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['90','92'])).

thf('94',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['89','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

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

thf('97',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X20 )
      | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ X20 @ X19 ) )
      | ( r2_waybel_7 @ X20 @ ( k2_yellow19 @ X20 @ X19 ) @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow19])).

thf('98',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r2_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('103',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('104',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

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

thf('106',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v1_subset_1 @ X22 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X23 ) ) ) )
      | ~ ( v2_waybel_0 @ X22 @ ( k3_yellow_1 @ ( k2_struct_0 @ X23 ) ) )
      | ~ ( v13_waybel_0 @ X22 @ ( k3_yellow_1 @ ( k2_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X23 ) ) ) ) )
      | ( X22
        = ( k2_yellow19 @ X23 @ ( k3_yellow19 @ X23 @ ( k2_struct_0 @ X23 ) @ X22 ) ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('107',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('108',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('109',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('110',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('111',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v1_subset_1 @ X22 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X23 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X22 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X23 ) ) ) )
      | ~ ( v13_waybel_0 @ X22 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X23 ) ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X23 ) ) ) ) ) )
      | ( X22
        = ( k2_yellow19 @ X23 @ ( k3_yellow19 @ X23 @ ( k2_struct_0 @ X23 ) @ X22 ) ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(demod,[status(thm)],['106','107','108','109','110'])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['105','111'])).

thf('113',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('114',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('115',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['104','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['103','123'])).

thf('125',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['102','124'])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','127'])).

thf('129',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['88','128'])).

thf('130',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['72','130'])).

thf('132',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','132'])).

thf('134',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('136',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('137',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ X10 ) )
      | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X10 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('138',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('139',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('140',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('141',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v2_waybel_0 @ X12 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) )
      | ~ ( v13_waybel_0 @ X12 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X11 @ X10 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['136','141'])).

thf('143',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('144',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['135','145'])).

thf('147',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['134','146'])).

thf('148',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','148'])).

thf('150',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('153',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['155','156'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('158',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('159',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['2','161'])).

thf('163',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['91'])).

thf('166',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('167',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('168',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('169',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('170',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['91'])).

thf('171',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('172',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('173',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('174',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('175',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('176',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('177',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('178',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('179',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X20 )
      | ~ ( r2_waybel_7 @ X20 @ ( k2_yellow19 @ X20 @ X19 ) @ X21 )
      | ( r2_hidden @ X21 @ ( k10_yellow_6 @ X20 @ X19 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow19])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['180','181','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['177','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['176','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['175','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['174','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['173','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['172','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['171','194'])).

thf('196',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['170','197'])).

thf('199',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('202',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('204',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('205',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('206',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('207',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v2_waybel_0 @ X12 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) )
      | ~ ( v13_waybel_0 @ X12 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X11 @ X10 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('210',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['208','209','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['205','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['204','212'])).

thf('214',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['203','215'])).

thf('217',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['202','216'])).

thf('218',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['169','218'])).

thf('220',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['219','220'])).

thf('222',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['168','221'])).

thf('223',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['167','223'])).

thf('225',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['224','225'])).

thf('227',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['226','227'])).

thf('229',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('232',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['232','233'])).

thf('235',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['166','234'])).

thf('236',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','164','165','237'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VDniEMmHUT
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:03:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 189 iterations in 0.080s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.55  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.37/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.55  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.37/0.55  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.37/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.37/0.55  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.37/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.55  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.37/0.55  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.37/0.55  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.37/0.55  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.37/0.55  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.37/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.55  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.55  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.37/0.55  thf(r2_waybel_7_type, type, r2_waybel_7: $i > $i > $i > $o).
% 0.37/0.55  thf(t18_yellow19, conjecture,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.55             ( v1_subset_1 @
% 0.37/0.55               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.37/0.55             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.55             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.55             ( m1_subset_1 @
% 0.37/0.55               B @ 
% 0.37/0.55               ( k1_zfmisc_1 @
% 0.37/0.55                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.37/0.55           ( ![C:$i]:
% 0.37/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.55               ( ( r2_hidden @
% 0.37/0.55                   C @ 
% 0.37/0.55                   ( k10_yellow_6 @
% 0.37/0.55                     A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) <=>
% 0.37/0.55                 ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i]:
% 0.37/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.55            ( l1_pre_topc @ A ) ) =>
% 0.37/0.55          ( ![B:$i]:
% 0.37/0.55            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.55                ( v1_subset_1 @
% 0.37/0.55                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.37/0.55                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.55                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.55                ( m1_subset_1 @
% 0.37/0.55                  B @ 
% 0.37/0.55                  ( k1_zfmisc_1 @
% 0.37/0.55                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.37/0.55              ( ![C:$i]:
% 0.37/0.55                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.55                  ( ( r2_hidden @
% 0.37/0.55                      C @ 
% 0.37/0.55                      ( k10_yellow_6 @
% 0.37/0.55                        A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) <=>
% 0.37/0.55                    ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t18_yellow19])).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      ((~ (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.37/0.55        | ~ (r2_hidden @ sk_C @ 
% 0.37/0.55             (k10_yellow_6 @ sk_A @ 
% 0.37/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.37/0.55       ~
% 0.37/0.55       ((r2_hidden @ sk_C @ 
% 0.37/0.55         (k10_yellow_6 @ sk_A @ 
% 0.37/0.55          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf(dt_l1_pre_topc, axiom,
% 0.37/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.37/0.55  thf('2', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.55  thf('3', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.55  thf('4', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.55  thf(d10_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.55  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.55      inference('simplify', [status(thm)], ['5'])).
% 0.37/0.55  thf(t3_subset, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X3 : $i, X5 : $i]:
% 0.37/0.55         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.55  thf('8', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.55  thf('9', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.55  thf(d3_struct_0, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X6 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ 
% 0.37/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(d2_yellow_1, axiom,
% 0.37/0.55    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.37/0.55      inference('demod', [status(thm)], ['11', '12'])).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      (((m1_subset_1 @ sk_B @ 
% 0.37/0.55         (k1_zfmisc_1 @ 
% 0.37/0.55          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 0.37/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.55      inference('sup+', [status(thm)], ['10', '13'])).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.55        | (m1_subset_1 @ sk_B @ 
% 0.37/0.55           (k1_zfmisc_1 @ 
% 0.37/0.55            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['9', '14'])).
% 0.37/0.55  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.37/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.55  thf(fc4_yellow19, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.37/0.55         ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.37/0.55         ( ~( v1_xboole_0 @ C ) ) & 
% 0.37/0.55         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.37/0.55         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.37/0.55         ( m1_subset_1 @
% 0.37/0.55           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.37/0.55       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.37/0.55         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.37/0.55         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.37/0.55         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.37/0.55          | (v1_xboole_0 @ X13)
% 0.37/0.55          | ~ (l1_struct_0 @ X14)
% 0.37/0.55          | (v2_struct_0 @ X14)
% 0.37/0.55          | (v1_xboole_0 @ X15)
% 0.37/0.55          | ~ (v2_waybel_0 @ X15 @ (k3_yellow_1 @ X13))
% 0.37/0.55          | ~ (v13_waybel_0 @ X15 @ (k3_yellow_1 @ X13))
% 0.37/0.55          | ~ (m1_subset_1 @ X15 @ 
% 0.37/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X13))))
% 0.37/0.55          | (v4_orders_2 @ (k3_yellow19 @ X14 @ X13 @ X15)))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.37/0.55          | (v1_xboole_0 @ X13)
% 0.37/0.55          | ~ (l1_struct_0 @ X14)
% 0.37/0.55          | (v2_struct_0 @ X14)
% 0.37/0.55          | (v1_xboole_0 @ X15)
% 0.37/0.55          | ~ (v2_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.37/0.55          | ~ (v13_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.37/0.55          | ~ (m1_subset_1 @ X15 @ 
% 0.37/0.55               (k1_zfmisc_1 @ 
% 0.37/0.55                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X13)))))
% 0.37/0.55          | (v4_orders_2 @ (k3_yellow19 @ X14 @ X13 @ X15)))),
% 0.37/0.55      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.55               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55          | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.55               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | ~ (l1_struct_0 @ X0)
% 0.37/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['17', '22'])).
% 0.37/0.55  thf('24', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X6 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (((v13_waybel_0 @ sk_B @ 
% 0.37/0.55         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.55      inference('sup+', [status(thm)], ['25', '28'])).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.55        | (v13_waybel_0 @ sk_B @ 
% 0.37/0.55           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['24', '29'])).
% 0.37/0.55  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.55        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['30', '31'])).
% 0.37/0.55  thf('33', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (![X6 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('37', plain,
% 0.37/0.55      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.37/0.55  thf('38', plain,
% 0.37/0.55      (((v2_waybel_0 @ sk_B @ 
% 0.37/0.55         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.55      inference('sup+', [status(thm)], ['34', '37'])).
% 0.37/0.55  thf('39', plain,
% 0.37/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.55        | (v2_waybel_0 @ sk_B @ 
% 0.37/0.55           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['33', '38'])).
% 0.37/0.55  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.55        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['39', '40'])).
% 0.37/0.55  thf('42', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | ~ (l1_struct_0 @ X0)
% 0.37/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.55      inference('demod', [status(thm)], ['23', '32', '41'])).
% 0.37/0.55  thf('43', plain,
% 0.37/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55        | (v2_struct_0 @ sk_A)
% 0.37/0.55        | (v1_xboole_0 @ sk_B)
% 0.37/0.55        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['8', '42'])).
% 0.37/0.55  thf('44', plain,
% 0.37/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.55        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55        | (v1_xboole_0 @ sk_B)
% 0.37/0.55        | (v2_struct_0 @ sk_A)
% 0.37/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['4', '43'])).
% 0.37/0.55  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('46', plain,
% 0.37/0.55      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55        | (v1_xboole_0 @ sk_B)
% 0.37/0.55        | (v2_struct_0 @ sk_A)
% 0.37/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['44', '45'])).
% 0.37/0.55  thf('47', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.55  thf('48', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.55  thf('49', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.37/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.55  thf(fc5_yellow19, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.37/0.55         ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.37/0.55         ( ~( v1_xboole_0 @ C ) ) & 
% 0.37/0.55         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.37/0.55         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.37/0.55         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.37/0.55         ( m1_subset_1 @
% 0.37/0.55           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.37/0.55       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.37/0.55         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.37/0.55         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.37/0.55  thf('50', plain,
% 0.37/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.55          | (v1_xboole_0 @ X16)
% 0.37/0.55          | ~ (l1_struct_0 @ X17)
% 0.37/0.55          | (v2_struct_0 @ X17)
% 0.37/0.55          | (v1_xboole_0 @ X18)
% 0.37/0.55          | ~ (v1_subset_1 @ X18 @ (u1_struct_0 @ (k3_yellow_1 @ X16)))
% 0.37/0.55          | ~ (v2_waybel_0 @ X18 @ (k3_yellow_1 @ X16))
% 0.37/0.55          | ~ (v13_waybel_0 @ X18 @ (k3_yellow_1 @ X16))
% 0.37/0.55          | ~ (m1_subset_1 @ X18 @ 
% 0.37/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X16))))
% 0.37/0.55          | (v7_waybel_0 @ (k3_yellow19 @ X17 @ X16 @ X18)))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.37/0.55  thf('51', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('52', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('53', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('54', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('55', plain,
% 0.37/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.55          | (v1_xboole_0 @ X16)
% 0.37/0.55          | ~ (l1_struct_0 @ X17)
% 0.37/0.55          | (v2_struct_0 @ X17)
% 0.37/0.55          | (v1_xboole_0 @ X18)
% 0.37/0.55          | ~ (v1_subset_1 @ X18 @ 
% 0.37/0.55               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X16))))
% 0.37/0.55          | ~ (v2_waybel_0 @ X18 @ (k3_lattice3 @ (k1_lattice3 @ X16)))
% 0.37/0.55          | ~ (v13_waybel_0 @ X18 @ (k3_lattice3 @ (k1_lattice3 @ X16)))
% 0.37/0.55          | ~ (m1_subset_1 @ X18 @ 
% 0.37/0.55               (k1_zfmisc_1 @ 
% 0.37/0.55                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X16)))))
% 0.37/0.55          | (v7_waybel_0 @ (k3_yellow19 @ X17 @ X16 @ X18)))),
% 0.37/0.55      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.37/0.55  thf('56', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.55               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55          | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.55               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55          | ~ (v1_subset_1 @ sk_B @ 
% 0.37/0.55               (u1_struct_0 @ 
% 0.37/0.55                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | ~ (l1_struct_0 @ X0)
% 0.37/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['49', '55'])).
% 0.37/0.55  thf('57', plain,
% 0.37/0.55      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.55        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['30', '31'])).
% 0.37/0.55  thf('58', plain,
% 0.37/0.55      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.55        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['39', '40'])).
% 0.37/0.55  thf('59', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.55  thf('60', plain,
% 0.37/0.55      (![X6 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('61', plain,
% 0.37/0.55      ((v1_subset_1 @ sk_B @ 
% 0.37/0.55        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('62', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('63', plain,
% 0.37/0.55      ((v1_subset_1 @ sk_B @ 
% 0.37/0.55        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.37/0.55      inference('demod', [status(thm)], ['61', '62'])).
% 0.37/0.55  thf('64', plain,
% 0.37/0.55      (((v1_subset_1 @ sk_B @ 
% 0.37/0.55         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.37/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.55      inference('sup+', [status(thm)], ['60', '63'])).
% 0.37/0.55  thf('65', plain,
% 0.37/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.55        | (v1_subset_1 @ sk_B @ 
% 0.37/0.55           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['59', '64'])).
% 0.37/0.55  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('67', plain,
% 0.37/0.55      ((v1_subset_1 @ sk_B @ 
% 0.37/0.55        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.55      inference('demod', [status(thm)], ['65', '66'])).
% 0.37/0.55  thf('68', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | ~ (l1_struct_0 @ X0)
% 0.37/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.55      inference('demod', [status(thm)], ['56', '57', '58', '67'])).
% 0.37/0.55  thf('69', plain,
% 0.37/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55        | (v2_struct_0 @ sk_A)
% 0.37/0.55        | (v1_xboole_0 @ sk_B)
% 0.37/0.55        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['48', '68'])).
% 0.37/0.55  thf('70', plain,
% 0.37/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.55        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55        | (v1_xboole_0 @ sk_B)
% 0.37/0.55        | (v2_struct_0 @ sk_A)
% 0.37/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['47', '69'])).
% 0.37/0.55  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('72', plain,
% 0.37/0.55      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55        | (v1_xboole_0 @ sk_B)
% 0.37/0.55        | (v2_struct_0 @ sk_A)
% 0.37/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['70', '71'])).
% 0.37/0.55  thf('73', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.55  thf('74', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.55  thf('75', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.37/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.55  thf(dt_k3_yellow19, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.37/0.55         ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.37/0.55         ( ~( v1_xboole_0 @ C ) ) & 
% 0.37/0.55         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.37/0.55         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.37/0.55         ( m1_subset_1 @
% 0.37/0.55           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.37/0.55       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.37/0.55         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.37/0.55         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.37/0.55  thf('76', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.55          | (v1_xboole_0 @ X10)
% 0.37/0.55          | ~ (l1_struct_0 @ X11)
% 0.37/0.55          | (v2_struct_0 @ X11)
% 0.37/0.55          | (v1_xboole_0 @ X12)
% 0.37/0.55          | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.37/0.55          | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.37/0.55          | ~ (m1_subset_1 @ X12 @ 
% 0.37/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X10))))
% 0.37/0.55          | (l1_waybel_0 @ (k3_yellow19 @ X11 @ X10 @ X12) @ X11))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.37/0.55  thf('77', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('78', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('79', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('80', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.55          | (v1_xboole_0 @ X10)
% 0.37/0.55          | ~ (l1_struct_0 @ X11)
% 0.37/0.55          | (v2_struct_0 @ X11)
% 0.37/0.55          | (v1_xboole_0 @ X12)
% 0.37/0.55          | ~ (v2_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.37/0.55          | ~ (v13_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.37/0.55          | ~ (m1_subset_1 @ X12 @ 
% 0.37/0.55               (k1_zfmisc_1 @ 
% 0.37/0.55                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X10)))))
% 0.37/0.55          | (l1_waybel_0 @ (k3_yellow19 @ X11 @ X10 @ X12) @ X11))),
% 0.37/0.55      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 0.37/0.55  thf('81', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.55          | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.55               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55          | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.55               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | ~ (l1_struct_0 @ X0)
% 0.37/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['75', '80'])).
% 0.37/0.55  thf('82', plain,
% 0.37/0.55      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.55        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['30', '31'])).
% 0.37/0.55  thf('83', plain,
% 0.37/0.55      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.55        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['39', '40'])).
% 0.37/0.55  thf('84', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | ~ (l1_struct_0 @ X0)
% 0.37/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.55      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.37/0.55  thf('85', plain,
% 0.37/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55        | (v2_struct_0 @ sk_A)
% 0.37/0.55        | (v1_xboole_0 @ sk_B)
% 0.37/0.55        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.55           sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['74', '84'])).
% 0.37/0.55  thf('86', plain,
% 0.37/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.55        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.55           sk_A)
% 0.37/0.55        | (v1_xboole_0 @ sk_B)
% 0.37/0.55        | (v2_struct_0 @ sk_A)
% 0.37/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['73', '85'])).
% 0.37/0.55  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('88', plain,
% 0.37/0.55      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.55         sk_A)
% 0.37/0.55        | (v1_xboole_0 @ sk_B)
% 0.37/0.55        | (v2_struct_0 @ sk_A)
% 0.37/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['86', '87'])).
% 0.37/0.55  thf('89', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.55  thf('90', plain,
% 0.37/0.55      (![X6 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('91', plain,
% 0.37/0.55      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.37/0.55        | (r2_hidden @ sk_C @ 
% 0.37/0.55           (k10_yellow_6 @ sk_A @ 
% 0.37/0.55            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('92', plain,
% 0.37/0.55      (((r2_hidden @ sk_C @ 
% 0.37/0.55         (k10_yellow_6 @ sk_A @ 
% 0.37/0.55          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.55         <= (((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('split', [status(esa)], ['91'])).
% 0.37/0.55  thf('93', plain,
% 0.37/0.55      ((((r2_hidden @ sk_C @ 
% 0.37/0.55          (k10_yellow_6 @ sk_A @ 
% 0.37/0.55           (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55         | ~ (l1_struct_0 @ sk_A)))
% 0.37/0.55         <= (((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('sup+', [status(thm)], ['90', '92'])).
% 0.37/0.55  thf('94', plain,
% 0.37/0.55      (((~ (l1_pre_topc @ sk_A)
% 0.37/0.55         | (r2_hidden @ sk_C @ 
% 0.37/0.55            (k10_yellow_6 @ sk_A @ 
% 0.37/0.55             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))))
% 0.37/0.55         <= (((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['89', '93'])).
% 0.37/0.55  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('96', plain,
% 0.37/0.55      (((r2_hidden @ sk_C @ 
% 0.37/0.55         (k10_yellow_6 @ sk_A @ 
% 0.37/0.55          (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.55         <= (((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('demod', [status(thm)], ['94', '95'])).
% 0.37/0.55  thf(t13_yellow19, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.37/0.55             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.37/0.55           ( ![C:$i]:
% 0.37/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.55               ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) <=>
% 0.37/0.55                 ( r2_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.37/0.55  thf('97', plain,
% 0.37/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.55         ((v2_struct_0 @ X19)
% 0.37/0.55          | ~ (v4_orders_2 @ X19)
% 0.37/0.55          | ~ (v7_waybel_0 @ X19)
% 0.37/0.55          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.37/0.55          | ~ (r2_hidden @ X21 @ (k10_yellow_6 @ X20 @ X19))
% 0.37/0.55          | (r2_waybel_7 @ X20 @ (k2_yellow19 @ X20 @ X19) @ X21)
% 0.37/0.55          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.37/0.55          | ~ (l1_pre_topc @ X20)
% 0.37/0.55          | ~ (v2_pre_topc @ X20)
% 0.37/0.55          | (v2_struct_0 @ X20))),
% 0.37/0.55      inference('cnf', [status(esa)], [t13_yellow19])).
% 0.37/0.55  thf('98', plain,
% 0.37/0.55      ((((v2_struct_0 @ sk_A)
% 0.37/0.55         | ~ (v2_pre_topc @ sk_A)
% 0.37/0.55         | ~ (l1_pre_topc @ sk_A)
% 0.37/0.55         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.37/0.55         | (r2_waybel_7 @ sk_A @ 
% 0.37/0.55            (k2_yellow19 @ sk_A @ 
% 0.37/0.55             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.37/0.55            sk_C)
% 0.37/0.55         | ~ (l1_waybel_0 @ 
% 0.37/0.55              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.37/0.55         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.55         <= (((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['96', '97'])).
% 0.37/0.55  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('101', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('102', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.55  thf('103', plain,
% 0.37/0.55      (![X6 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('104', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.55  thf('105', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.37/0.55      inference('demod', [status(thm)], ['11', '12'])).
% 0.37/0.55  thf(t15_yellow19, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.55             ( v1_subset_1 @
% 0.37/0.55               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.37/0.55             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.55             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.55             ( m1_subset_1 @
% 0.37/0.55               B @ 
% 0.37/0.55               ( k1_zfmisc_1 @
% 0.37/0.55                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.37/0.55           ( ( B ) =
% 0.37/0.55             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.37/0.55  thf('106', plain,
% 0.37/0.55      (![X22 : $i, X23 : $i]:
% 0.37/0.55         ((v1_xboole_0 @ X22)
% 0.37/0.55          | ~ (v1_subset_1 @ X22 @ 
% 0.37/0.55               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X23))))
% 0.37/0.55          | ~ (v2_waybel_0 @ X22 @ (k3_yellow_1 @ (k2_struct_0 @ X23)))
% 0.37/0.55          | ~ (v13_waybel_0 @ X22 @ (k3_yellow_1 @ (k2_struct_0 @ X23)))
% 0.37/0.55          | ~ (m1_subset_1 @ X22 @ 
% 0.37/0.55               (k1_zfmisc_1 @ 
% 0.37/0.55                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X23)))))
% 0.37/0.55          | ((X22)
% 0.37/0.55              = (k2_yellow19 @ X23 @ 
% 0.37/0.55                 (k3_yellow19 @ X23 @ (k2_struct_0 @ X23) @ X22)))
% 0.37/0.55          | ~ (l1_struct_0 @ X23)
% 0.37/0.55          | (v2_struct_0 @ X23))),
% 0.37/0.55      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.37/0.55  thf('107', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('108', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('109', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('110', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('111', plain,
% 0.37/0.55      (![X22 : $i, X23 : $i]:
% 0.37/0.55         ((v1_xboole_0 @ X22)
% 0.37/0.55          | ~ (v1_subset_1 @ X22 @ 
% 0.37/0.55               (u1_struct_0 @ 
% 0.37/0.55                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X23)))))
% 0.37/0.55          | ~ (v2_waybel_0 @ X22 @ 
% 0.37/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X23))))
% 0.37/0.55          | ~ (v13_waybel_0 @ X22 @ 
% 0.37/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X23))))
% 0.37/0.55          | ~ (m1_subset_1 @ X22 @ 
% 0.37/0.55               (k1_zfmisc_1 @ 
% 0.37/0.55                (u1_struct_0 @ 
% 0.37/0.55                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X23))))))
% 0.37/0.55          | ((X22)
% 0.37/0.55              = (k2_yellow19 @ X23 @ 
% 0.37/0.55                 (k3_yellow19 @ X23 @ (k2_struct_0 @ X23) @ X22)))
% 0.37/0.55          | ~ (l1_struct_0 @ X23)
% 0.37/0.55          | (v2_struct_0 @ X23))),
% 0.37/0.55      inference('demod', [status(thm)], ['106', '107', '108', '109', '110'])).
% 0.37/0.55  thf('112', plain,
% 0.37/0.55      (((v2_struct_0 @ sk_A)
% 0.37/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55        | ((sk_B)
% 0.37/0.55            = (k2_yellow19 @ sk_A @ 
% 0.37/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55        | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.55             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.55        | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.55             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.55        | ~ (v1_subset_1 @ sk_B @ 
% 0.37/0.55             (u1_struct_0 @ 
% 0.37/0.55              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.37/0.55        | (v1_xboole_0 @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['105', '111'])).
% 0.37/0.55  thf('113', plain,
% 0.37/0.55      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.37/0.55  thf('114', plain,
% 0.37/0.55      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.37/0.55  thf('115', plain,
% 0.37/0.55      ((v1_subset_1 @ sk_B @ 
% 0.37/0.55        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.37/0.55      inference('demod', [status(thm)], ['61', '62'])).
% 0.37/0.55  thf('116', plain,
% 0.37/0.55      (((v2_struct_0 @ sk_A)
% 0.37/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55        | ((sk_B)
% 0.37/0.55            = (k2_yellow19 @ sk_A @ 
% 0.37/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55        | (v1_xboole_0 @ sk_B))),
% 0.37/0.55      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 0.37/0.55  thf('117', plain,
% 0.37/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.55        | (v1_xboole_0 @ sk_B)
% 0.37/0.55        | ((sk_B)
% 0.37/0.55            = (k2_yellow19 @ sk_A @ 
% 0.37/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55        | (v2_struct_0 @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['104', '116'])).
% 0.37/0.55  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('119', plain,
% 0.37/0.55      (((v1_xboole_0 @ sk_B)
% 0.37/0.55        | ((sk_B)
% 0.37/0.55            = (k2_yellow19 @ sk_A @ 
% 0.37/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55        | (v2_struct_0 @ sk_A))),
% 0.37/0.55      inference('demod', [status(thm)], ['117', '118'])).
% 0.37/0.55  thf('120', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('121', plain,
% 0.37/0.55      (((v2_struct_0 @ sk_A)
% 0.37/0.55        | ((sk_B)
% 0.37/0.55            = (k2_yellow19 @ sk_A @ 
% 0.37/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.37/0.55      inference('clc', [status(thm)], ['119', '120'])).
% 0.37/0.55  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('123', plain,
% 0.37/0.55      (((sk_B)
% 0.37/0.55         = (k2_yellow19 @ sk_A @ 
% 0.37/0.55            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.55      inference('clc', [status(thm)], ['121', '122'])).
% 0.37/0.55  thf('124', plain,
% 0.37/0.55      ((((sk_B)
% 0.37/0.55          = (k2_yellow19 @ sk_A @ 
% 0.37/0.55             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.55      inference('sup+', [status(thm)], ['103', '123'])).
% 0.37/0.55  thf('125', plain,
% 0.37/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.55        | ((sk_B)
% 0.37/0.55            = (k2_yellow19 @ sk_A @ 
% 0.37/0.55               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['102', '124'])).
% 0.37/0.55  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('127', plain,
% 0.37/0.55      (((sk_B)
% 0.37/0.55         = (k2_yellow19 @ sk_A @ 
% 0.37/0.55            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.55      inference('demod', [status(thm)], ['125', '126'])).
% 0.37/0.55  thf('128', plain,
% 0.37/0.55      ((((v2_struct_0 @ sk_A)
% 0.37/0.55         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.37/0.55         | ~ (l1_waybel_0 @ 
% 0.37/0.55              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.37/0.55         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.55         <= (((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('demod', [status(thm)], ['98', '99', '100', '101', '127'])).
% 0.37/0.55  thf('129', plain,
% 0.37/0.55      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55         | (v2_struct_0 @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ sk_B)
% 0.37/0.55         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.37/0.55         | (v2_struct_0 @ sk_A)))
% 0.37/0.55         <= (((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['88', '128'])).
% 0.37/0.55  thf('130', plain,
% 0.37/0.55      ((((r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.37/0.55         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55         | (v1_xboole_0 @ sk_B)
% 0.37/0.55         | (v2_struct_0 @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55         <= (((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('simplify', [status(thm)], ['129'])).
% 0.37/0.55  thf('131', plain,
% 0.37/0.55      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55         | (v2_struct_0 @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ sk_B)
% 0.37/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55         | (v2_struct_0 @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ sk_B)
% 0.37/0.55         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.37/0.55         <= (((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['72', '130'])).
% 0.37/0.55  thf('132', plain,
% 0.37/0.55      ((((r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.37/0.55         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55         | (v1_xboole_0 @ sk_B)
% 0.37/0.55         | (v2_struct_0 @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55         <= (((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('simplify', [status(thm)], ['131'])).
% 0.37/0.55  thf('133', plain,
% 0.37/0.55      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55         | (v2_struct_0 @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ sk_B)
% 0.37/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55         | (v2_struct_0 @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ sk_B)
% 0.37/0.55         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.37/0.55         <= (((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['46', '132'])).
% 0.37/0.55  thf('134', plain,
% 0.37/0.55      ((((r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.37/0.55         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55         | (v1_xboole_0 @ sk_B)
% 0.37/0.55         | (v2_struct_0 @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55         <= (((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('simplify', [status(thm)], ['133'])).
% 0.37/0.55  thf('135', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.55  thf('136', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.37/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.55  thf('137', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.55          | (v1_xboole_0 @ X10)
% 0.37/0.55          | ~ (l1_struct_0 @ X11)
% 0.37/0.55          | (v2_struct_0 @ X11)
% 0.37/0.55          | (v1_xboole_0 @ X12)
% 0.37/0.55          | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.37/0.55          | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.37/0.55          | ~ (m1_subset_1 @ X12 @ 
% 0.37/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X10))))
% 0.37/0.55          | ~ (v2_struct_0 @ (k3_yellow19 @ X11 @ X10 @ X12)))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.37/0.55  thf('138', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('139', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('140', plain,
% 0.37/0.55      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.55  thf('141', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.55          | (v1_xboole_0 @ X10)
% 0.37/0.55          | ~ (l1_struct_0 @ X11)
% 0.37/0.55          | (v2_struct_0 @ X11)
% 0.37/0.55          | (v1_xboole_0 @ X12)
% 0.37/0.55          | ~ (v2_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.37/0.55          | ~ (v13_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.37/0.55          | ~ (m1_subset_1 @ X12 @ 
% 0.37/0.55               (k1_zfmisc_1 @ 
% 0.37/0.55                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X10)))))
% 0.37/0.55          | ~ (v2_struct_0 @ (k3_yellow19 @ X11 @ X10 @ X12)))),
% 0.37/0.55      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 0.37/0.55  thf('142', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.55               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55          | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.55               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | ~ (l1_struct_0 @ X0)
% 0.37/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['136', '141'])).
% 0.37/0.55  thf('143', plain,
% 0.37/0.55      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.55        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['30', '31'])).
% 0.37/0.55  thf('144', plain,
% 0.37/0.55      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.55        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['39', '40'])).
% 0.37/0.55  thf('145', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | ~ (l1_struct_0 @ X0)
% 0.37/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.55      inference('demod', [status(thm)], ['142', '143', '144'])).
% 0.37/0.55  thf('146', plain,
% 0.37/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55        | (v2_struct_0 @ sk_A)
% 0.37/0.55        | (v1_xboole_0 @ sk_B)
% 0.37/0.55        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['135', '145'])).
% 0.37/0.55  thf('147', plain,
% 0.37/0.55      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55         | (v2_struct_0 @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ sk_B)
% 0.37/0.55         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.37/0.55         | (v1_xboole_0 @ sk_B)
% 0.37/0.55         | (v2_struct_0 @ sk_A)
% 0.37/0.55         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55         <= (((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['134', '146'])).
% 0.37/0.55  thf('148', plain,
% 0.37/0.55      (((~ (l1_struct_0 @ sk_A)
% 0.37/0.55         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.37/0.55         | (v1_xboole_0 @ sk_B)
% 0.37/0.55         | (v2_struct_0 @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55         <= (((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('simplify', [status(thm)], ['147'])).
% 0.37/0.55  thf('149', plain,
% 0.37/0.55      (((~ (l1_pre_topc @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55         | (v2_struct_0 @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ sk_B)
% 0.37/0.55         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.37/0.55         <= (((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['3', '148'])).
% 0.37/0.55  thf('150', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('151', plain,
% 0.37/0.55      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55         | (v2_struct_0 @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ sk_B)
% 0.37/0.55         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.37/0.55         <= (((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('demod', [status(thm)], ['149', '150'])).
% 0.37/0.55  thf('152', plain,
% 0.37/0.55      ((~ (r2_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.37/0.55         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('153', plain,
% 0.37/0.55      ((((v1_xboole_0 @ sk_B)
% 0.37/0.55         | (v2_struct_0 @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.37/0.55             ((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['151', '152'])).
% 0.37/0.55  thf('154', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('155', plain,
% 0.37/0.55      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.37/0.55         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.37/0.55             ((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('clc', [status(thm)], ['153', '154'])).
% 0.37/0.55  thf('156', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('157', plain,
% 0.37/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.37/0.55         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.37/0.55             ((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('clc', [status(thm)], ['155', '156'])).
% 0.37/0.55  thf(fc2_struct_0, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.55       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.55  thf('158', plain,
% 0.37/0.55      (![X8 : $i]:
% 0.37/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.37/0.55          | ~ (l1_struct_0 @ X8)
% 0.37/0.55          | (v2_struct_0 @ X8))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.37/0.55  thf('159', plain,
% 0.37/0.55      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.37/0.55         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.37/0.55             ((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['157', '158'])).
% 0.37/0.55  thf('160', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('161', plain,
% 0.37/0.55      ((~ (l1_struct_0 @ sk_A))
% 0.37/0.55         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.37/0.55             ((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('clc', [status(thm)], ['159', '160'])).
% 0.37/0.55  thf('162', plain,
% 0.37/0.55      ((~ (l1_pre_topc @ sk_A))
% 0.37/0.55         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.37/0.55             ((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['2', '161'])).
% 0.37/0.55  thf('163', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('164', plain,
% 0.37/0.55      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.37/0.55       ~
% 0.37/0.55       ((r2_hidden @ sk_C @ 
% 0.37/0.55         (k10_yellow_6 @ sk_A @ 
% 0.37/0.55          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.37/0.55      inference('demod', [status(thm)], ['162', '163'])).
% 0.37/0.55  thf('165', plain,
% 0.37/0.55      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.37/0.55       ((r2_hidden @ sk_C @ 
% 0.37/0.55         (k10_yellow_6 @ sk_A @ 
% 0.37/0.55          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.37/0.55      inference('split', [status(esa)], ['91'])).
% 0.37/0.55  thf('166', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.55  thf('167', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.55  thf('168', plain,
% 0.37/0.55      (![X6 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('169', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.55  thf('170', plain,
% 0.37/0.55      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.37/0.55         <= (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.55      inference('split', [status(esa)], ['91'])).
% 0.37/0.55  thf('171', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.55  thf('172', plain,
% 0.37/0.55      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55        | (v1_xboole_0 @ sk_B)
% 0.37/0.55        | (v2_struct_0 @ sk_A)
% 0.37/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['70', '71'])).
% 0.37/0.55  thf('173', plain,
% 0.37/0.55      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55        | (v1_xboole_0 @ sk_B)
% 0.37/0.55        | (v2_struct_0 @ sk_A)
% 0.37/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['44', '45'])).
% 0.37/0.55  thf('174', plain,
% 0.37/0.55      (![X6 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('175', plain,
% 0.37/0.55      (![X6 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('176', plain,
% 0.37/0.55      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.55         sk_A)
% 0.37/0.55        | (v1_xboole_0 @ sk_B)
% 0.37/0.55        | (v2_struct_0 @ sk_A)
% 0.37/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['86', '87'])).
% 0.37/0.55  thf('177', plain,
% 0.37/0.55      (![X6 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('178', plain,
% 0.37/0.55      (((sk_B)
% 0.37/0.55         = (k2_yellow19 @ sk_A @ 
% 0.37/0.55            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.55      inference('clc', [status(thm)], ['121', '122'])).
% 0.37/0.55  thf('179', plain,
% 0.37/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.55         ((v2_struct_0 @ X19)
% 0.37/0.55          | ~ (v4_orders_2 @ X19)
% 0.37/0.55          | ~ (v7_waybel_0 @ X19)
% 0.37/0.55          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.37/0.55          | ~ (r2_waybel_7 @ X20 @ (k2_yellow19 @ X20 @ X19) @ X21)
% 0.37/0.55          | (r2_hidden @ X21 @ (k10_yellow_6 @ X20 @ X19))
% 0.37/0.55          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.37/0.55          | ~ (l1_pre_topc @ X20)
% 0.37/0.55          | ~ (v2_pre_topc @ X20)
% 0.37/0.55          | (v2_struct_0 @ X20))),
% 0.37/0.55      inference('cnf', [status(esa)], [t13_yellow19])).
% 0.37/0.55  thf('180', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.55          | (v2_struct_0 @ sk_A)
% 0.37/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | (r2_hidden @ X0 @ 
% 0.37/0.55             (k10_yellow_6 @ sk_A @ 
% 0.37/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55          | ~ (l1_waybel_0 @ 
% 0.37/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.37/0.55          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['178', '179'])).
% 0.37/0.55  thf('181', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('182', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('183', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.55          | (v2_struct_0 @ sk_A)
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | (r2_hidden @ X0 @ 
% 0.37/0.55             (k10_yellow_6 @ sk_A @ 
% 0.37/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55          | ~ (l1_waybel_0 @ 
% 0.37/0.55               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.37/0.55          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.55      inference('demod', [status(thm)], ['180', '181', '182'])).
% 0.37/0.55  thf('184', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (l1_waybel_0 @ 
% 0.37/0.55             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.37/0.55          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | (r2_hidden @ X0 @ 
% 0.37/0.55             (k10_yellow_6 @ sk_A @ 
% 0.37/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | (v2_struct_0 @ sk_A)
% 0.37/0.55          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['177', '183'])).
% 0.37/0.55  thf('185', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | (v2_struct_0 @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.55          | (v2_struct_0 @ sk_A)
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | (r2_hidden @ X0 @ 
% 0.37/0.55             (k10_yellow_6 @ sk_A @ 
% 0.37/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['176', '184'])).
% 0.37/0.55  thf('186', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (l1_struct_0 @ sk_A)
% 0.37/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | (r2_hidden @ X0 @ 
% 0.37/0.55             (k10_yellow_6 @ sk_A @ 
% 0.37/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | (v2_struct_0 @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['185'])).
% 0.37/0.55  thf('187', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | (v2_struct_0 @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | (r2_hidden @ X0 @ 
% 0.37/0.55             (k10_yellow_6 @ sk_A @ 
% 0.37/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['175', '186'])).
% 0.37/0.55  thf('188', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | (r2_hidden @ X0 @ 
% 0.37/0.55             (k10_yellow_6 @ sk_A @ 
% 0.37/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | (v2_struct_0 @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['187'])).
% 0.37/0.55  thf('189', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | (v2_struct_0 @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | (r2_hidden @ X0 @ 
% 0.37/0.55             (k10_yellow_6 @ sk_A @ 
% 0.37/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['174', '188'])).
% 0.37/0.55  thf('190', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | (r2_hidden @ X0 @ 
% 0.37/0.55             (k10_yellow_6 @ sk_A @ 
% 0.37/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | (v2_struct_0 @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['189'])).
% 0.37/0.55  thf('191', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | (v2_struct_0 @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | (v2_struct_0 @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | (r2_hidden @ X0 @ 
% 0.37/0.55             (k10_yellow_6 @ sk_A @ 
% 0.37/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['173', '190'])).
% 0.37/0.55  thf('192', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | (r2_hidden @ X0 @ 
% 0.37/0.55             (k10_yellow_6 @ sk_A @ 
% 0.37/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.55          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | (v2_struct_0 @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['191'])).
% 0.37/0.55  thf('193', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | (v2_struct_0 @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | (v2_struct_0 @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | (r2_hidden @ X0 @ 
% 0.37/0.55             (k10_yellow_6 @ sk_A @ 
% 0.37/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['172', '192'])).
% 0.37/0.55  thf('194', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | (r2_hidden @ X0 @ 
% 0.37/0.55             (k10_yellow_6 @ sk_A @ 
% 0.37/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.55          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | (v2_struct_0 @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['193'])).
% 0.37/0.55  thf('195', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (l1_pre_topc @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | (v2_struct_0 @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | (r2_hidden @ X0 @ 
% 0.37/0.55             (k10_yellow_6 @ sk_A @ 
% 0.37/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['171', '194'])).
% 0.37/0.55  thf('196', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('197', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | (v2_struct_0 @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55          | (r2_hidden @ X0 @ 
% 0.37/0.55             (k10_yellow_6 @ sk_A @ 
% 0.37/0.55              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.55      inference('demod', [status(thm)], ['195', '196'])).
% 0.37/0.55  thf('198', plain,
% 0.37/0.55      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55         | (r2_hidden @ sk_C @ 
% 0.37/0.55            (k10_yellow_6 @ sk_A @ 
% 0.37/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.37/0.55         | (v1_xboole_0 @ sk_B)
% 0.37/0.55         | (v2_struct_0 @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55         <= (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['170', '197'])).
% 0.37/0.55  thf('199', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('200', plain,
% 0.37/0.55      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55         | (r2_hidden @ sk_C @ 
% 0.37/0.55            (k10_yellow_6 @ sk_A @ 
% 0.37/0.55             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.55         | (v1_xboole_0 @ sk_B)
% 0.37/0.55         | (v2_struct_0 @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55         <= (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.55      inference('demod', [status(thm)], ['198', '199'])).
% 0.37/0.55  thf('201', plain,
% 0.37/0.55      ((~ (r2_hidden @ sk_C @ 
% 0.37/0.55           (k10_yellow_6 @ sk_A @ 
% 0.37/0.55            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('202', plain,
% 0.37/0.55      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55         | (v2_struct_0 @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ sk_B)
% 0.37/0.55         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.55             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['200', '201'])).
% 0.37/0.55  thf('203', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.55  thf('204', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.55  thf('205', plain,
% 0.37/0.55      (![X6 : $i]:
% 0.37/0.55         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.55  thf('206', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ 
% 0.37/0.55        (k1_zfmisc_1 @ 
% 0.37/0.55         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.37/0.55      inference('demod', [status(thm)], ['11', '12'])).
% 0.37/0.55  thf('207', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.55          | (v1_xboole_0 @ X10)
% 0.37/0.55          | ~ (l1_struct_0 @ X11)
% 0.37/0.55          | (v2_struct_0 @ X11)
% 0.37/0.55          | (v1_xboole_0 @ X12)
% 0.37/0.55          | ~ (v2_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.37/0.55          | ~ (v13_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.37/0.55          | ~ (m1_subset_1 @ X12 @ 
% 0.37/0.55               (k1_zfmisc_1 @ 
% 0.37/0.55                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X10)))))
% 0.37/0.55          | ~ (v2_struct_0 @ (k3_yellow19 @ X11 @ X10 @ X12)))),
% 0.37/0.55      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 0.37/0.55  thf('208', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.55          | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.55               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | ~ (l1_struct_0 @ X0)
% 0.37/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.55          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['206', '207'])).
% 0.37/0.55  thf('209', plain,
% 0.37/0.55      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.37/0.55  thf('210', plain,
% 0.37/0.55      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.55        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.37/0.55  thf('211', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | ~ (l1_struct_0 @ X0)
% 0.37/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.55          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.55      inference('demod', [status(thm)], ['208', '209', '210'])).
% 0.37/0.55  thf('212', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.37/0.55          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.55          | ~ (l1_struct_0 @ X0)
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['205', '211'])).
% 0.37/0.55  thf('213', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (l1_pre_topc @ sk_A)
% 0.37/0.55          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | ~ (l1_struct_0 @ X0)
% 0.37/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['204', '212'])).
% 0.37/0.55  thf('214', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('215', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.55          | (v1_xboole_0 @ sk_B)
% 0.37/0.55          | (v2_struct_0 @ X0)
% 0.37/0.55          | ~ (l1_struct_0 @ X0)
% 0.37/0.55          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.55      inference('demod', [status(thm)], ['213', '214'])).
% 0.37/0.55  thf('216', plain,
% 0.37/0.55      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55        | (v2_struct_0 @ sk_A)
% 0.37/0.55        | (v1_xboole_0 @ sk_B)
% 0.37/0.55        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['203', '215'])).
% 0.37/0.55  thf('217', plain,
% 0.37/0.55      ((((v1_xboole_0 @ sk_B)
% 0.37/0.55         | (v2_struct_0 @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55         | (v1_xboole_0 @ sk_B)
% 0.37/0.55         | (v2_struct_0 @ sk_A)
% 0.37/0.55         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.55         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ sk_C @ 
% 0.37/0.55               (k10_yellow_6 @ sk_A @ 
% 0.37/0.55                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.55             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['202', '216'])).
% 0.37/0.55  thf('218', plain,
% 0.37/0.55      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.55         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['217'])).
% 0.37/0.56  thf('219', plain,
% 0.37/0.56      (((~ (l1_pre_topc @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['169', '218'])).
% 0.37/0.56  thf('220', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('221', plain,
% 0.37/0.56      ((((v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.56      inference('demod', [status(thm)], ['219', '220'])).
% 0.37/0.56  thf('222', plain,
% 0.37/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['168', '221'])).
% 0.37/0.56  thf('223', plain,
% 0.37/0.56      ((((v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['222'])).
% 0.37/0.56  thf('224', plain,
% 0.37/0.56      (((~ (l1_pre_topc @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['167', '223'])).
% 0.37/0.56  thf('225', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('226', plain,
% 0.37/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.56      inference('demod', [status(thm)], ['224', '225'])).
% 0.37/0.56  thf('227', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('228', plain,
% 0.37/0.56      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.56      inference('clc', [status(thm)], ['226', '227'])).
% 0.37/0.56  thf('229', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('230', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.56      inference('clc', [status(thm)], ['228', '229'])).
% 0.37/0.56  thf('231', plain,
% 0.37/0.56      (![X8 : $i]:
% 0.37/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.37/0.56          | ~ (l1_struct_0 @ X8)
% 0.37/0.56          | (v2_struct_0 @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.37/0.56  thf('232', plain,
% 0.37/0.56      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['230', '231'])).
% 0.37/0.56  thf('233', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('234', plain,
% 0.37/0.56      ((~ (l1_struct_0 @ sk_A))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.56      inference('clc', [status(thm)], ['232', '233'])).
% 0.37/0.56  thf('235', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['166', '234'])).
% 0.37/0.56  thf('236', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('237', plain,
% 0.37/0.56      (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.37/0.56       ((r2_hidden @ sk_C @ 
% 0.37/0.56         (k10_yellow_6 @ sk_A @ 
% 0.37/0.56          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.37/0.56      inference('demod', [status(thm)], ['235', '236'])).
% 0.37/0.56  thf('238', plain, ($false),
% 0.37/0.56      inference('sat_resolution*', [status(thm)], ['1', '164', '165', '237'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
