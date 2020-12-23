%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qkLJaLa0Sb

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:49 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  285 ( 906 expanded)
%              Number of leaves         :   40 ( 294 expanded)
%              Depth                    :   42
%              Number of atoms          : 3797 (16067 expanded)
%              Number of equality atoms :   50 ( 237 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

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

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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

thf('18',plain,(
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
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('23',plain,(
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
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
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
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('26',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('29',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('35',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('38',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('44',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('47',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['24','33','42','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','52'])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('59',plain,(
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

thf('60',plain,(
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

thf('61',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('62',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('63',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('64',plain,(
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
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('67',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','68'])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
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
    inference(demod,[status(thm)],['31','32'])).

thf('83',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

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
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['91'])).

thf('93',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['90','92'])).

thf('94',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['89','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
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

thf('98',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X20 )
      | ~ ( r3_waybel_9 @ X20 @ X19 @ X21 )
      | ( r1_waybel_7 @ X20 @ ( k2_yellow19 @ X20 @ X19 ) @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('99',plain,(
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
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['96','102'])).

thf('104',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['88','103'])).

thf('105',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['72','105'])).

thf('107',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('108',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('109',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('110',plain,(
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

thf('111',plain,(
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

thf('112',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('113',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('114',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('115',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('116',plain,(
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
    inference(demod,[status(thm)],['111','112','113','114','115'])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['110','116'])).

thf('118',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('119',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('120',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('122',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['109','121'])).

thf('123',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['108','128'])).

thf('130',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['107','129'])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['106','132'])).

thf('134',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['56','134'])).

thf('136',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('138',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('139',plain,(
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

thf('140',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('141',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('142',plain,(
    ! [X9: $i] :
      ( ( k3_yellow_1 @ X9 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('143',plain,(
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
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['138','143'])).

thf('145',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('146',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['137','147'])).

thf('149',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['136','148'])).

thf('150',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['3','150'])).

thf('152',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('155',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('161',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['159','163'])).

thf('165',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','166'])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['91'])).

thf('171',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('172',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('173',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('174',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('175',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['91'])).

thf('176',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('177',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('178',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('179',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('180',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('181',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('182',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('183',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('184',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X20 )
      | ~ ( r1_waybel_7 @ X20 @ ( k2_yellow19 @ X20 @ X19 ) @ X21 )
      | ( r3_waybel_9 @ X20 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('185',plain,(
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
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['182','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['181','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['180','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['179','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['178','195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['177','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['176','199'])).

thf('201',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['175','202'])).

thf('204',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('207',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('209',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('210',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('211',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('212',plain,(
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
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('215',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['213','214','215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['210','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['209','217'])).

thf('219',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['208','220'])).

thf('222',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['207','221'])).

thf('223',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['174','223'])).

thf('225',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['224','225'])).

thf('227',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['173','226'])).

thf('228',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['172','228'])).

thf('230',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['231','232'])).

thf('234',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('237',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('240',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['171','239'])).

thf('241',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('243',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','169','170','242'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qkLJaLa0Sb
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 21:00:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 198 iterations in 0.136s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.37/0.61  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.37/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.61  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.37/0.61  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.37/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.61  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.37/0.61  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.37/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.61  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.37/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.61  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.37/0.61  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.37/0.61  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.37/0.61  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.37/0.61  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.37/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.61  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.37/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.61  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 0.37/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.61  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.37/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.61  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.37/0.61  thf(t17_yellow19, conjecture,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.61             ( v1_subset_1 @
% 0.37/0.61               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.37/0.61             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.61             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.61             ( m1_subset_1 @
% 0.37/0.61               B @ 
% 0.37/0.61               ( k1_zfmisc_1 @
% 0.37/0.61                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.37/0.61           ( ![C:$i]:
% 0.37/0.61             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.61               ( ( r3_waybel_9 @
% 0.37/0.61                   A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.37/0.61                 ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i]:
% 0.37/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.61            ( l1_pre_topc @ A ) ) =>
% 0.37/0.61          ( ![B:$i]:
% 0.37/0.61            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.61                ( v1_subset_1 @
% 0.37/0.61                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.37/0.61                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.61                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.61                ( m1_subset_1 @
% 0.37/0.61                  B @ 
% 0.37/0.61                  ( k1_zfmisc_1 @
% 0.37/0.61                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.37/0.61              ( ![C:$i]:
% 0.37/0.61                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.61                  ( ( r3_waybel_9 @
% 0.37/0.61                      A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.37/0.61                    ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t17_yellow19])).
% 0.37/0.61  thf('0', plain,
% 0.37/0.61      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.37/0.61        | ~ (r3_waybel_9 @ sk_A @ 
% 0.37/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.37/0.61       ~
% 0.37/0.61       ((r3_waybel_9 @ sk_A @ 
% 0.37/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.37/0.61      inference('split', [status(esa)], ['0'])).
% 0.37/0.61  thf(dt_l1_pre_topc, axiom,
% 0.37/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.37/0.61  thf('2', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.61  thf('3', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.61  thf('4', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.61  thf(d10_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.61  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.61      inference('simplify', [status(thm)], ['5'])).
% 0.37/0.61  thf(t3_subset, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.61  thf('7', plain,
% 0.37/0.61      (![X3 : $i, X5 : $i]:
% 0.37/0.61         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.61  thf('8', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.61  thf('9', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.61  thf(d3_struct_0, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.37/0.61  thf('10', plain,
% 0.37/0.61      (![X6 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('11', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B @ 
% 0.37/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(d2_yellow_1, axiom,
% 0.37/0.61    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.37/0.61  thf('12', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('13', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.37/0.61      inference('demod', [status(thm)], ['11', '12'])).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (((m1_subset_1 @ sk_B @ 
% 0.37/0.61         (k1_zfmisc_1 @ 
% 0.37/0.61          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup+', [status(thm)], ['10', '13'])).
% 0.37/0.61  thf('15', plain,
% 0.37/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | (m1_subset_1 @ sk_B @ 
% 0.37/0.61           (k1_zfmisc_1 @ 
% 0.37/0.61            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['9', '14'])).
% 0.37/0.61  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('17', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.37/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.61  thf(fc5_yellow19, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.37/0.61         ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.37/0.61         ( ~( v1_xboole_0 @ C ) ) & 
% 0.37/0.61         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.37/0.61         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.37/0.61         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.37/0.61         ( m1_subset_1 @
% 0.37/0.61           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.37/0.61       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.37/0.61         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.37/0.61         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.37/0.61  thf('18', plain,
% 0.37/0.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.61          | (v1_xboole_0 @ X16)
% 0.37/0.61          | ~ (l1_struct_0 @ X17)
% 0.37/0.61          | (v2_struct_0 @ X17)
% 0.37/0.61          | (v1_xboole_0 @ X18)
% 0.37/0.61          | ~ (v1_subset_1 @ X18 @ (u1_struct_0 @ (k3_yellow_1 @ X16)))
% 0.37/0.61          | ~ (v2_waybel_0 @ X18 @ (k3_yellow_1 @ X16))
% 0.37/0.61          | ~ (v13_waybel_0 @ X18 @ (k3_yellow_1 @ X16))
% 0.37/0.61          | ~ (m1_subset_1 @ X18 @ 
% 0.37/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X16))))
% 0.37/0.61          | (v7_waybel_0 @ (k3_yellow19 @ X17 @ X16 @ X18)))),
% 0.37/0.61      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.37/0.61  thf('19', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('20', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('21', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('22', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('23', plain,
% 0.37/0.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.61          | (v1_xboole_0 @ X16)
% 0.37/0.61          | ~ (l1_struct_0 @ X17)
% 0.37/0.61          | (v2_struct_0 @ X17)
% 0.37/0.61          | (v1_xboole_0 @ X18)
% 0.37/0.61          | ~ (v1_subset_1 @ X18 @ 
% 0.37/0.61               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X16))))
% 0.37/0.61          | ~ (v2_waybel_0 @ X18 @ (k3_lattice3 @ (k1_lattice3 @ X16)))
% 0.37/0.61          | ~ (v13_waybel_0 @ X18 @ (k3_lattice3 @ (k1_lattice3 @ X16)))
% 0.37/0.61          | ~ (m1_subset_1 @ X18 @ 
% 0.37/0.61               (k1_zfmisc_1 @ 
% 0.37/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X16)))))
% 0.37/0.61          | (v7_waybel_0 @ (k3_yellow19 @ X17 @ X16 @ X18)))),
% 0.37/0.61      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.37/0.61  thf('24', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61          | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.61          | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.61          | ~ (v1_subset_1 @ sk_B @ 
% 0.37/0.61               (u1_struct_0 @ 
% 0.37/0.61                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.37/0.61          | (v1_xboole_0 @ sk_B)
% 0.37/0.61          | (v2_struct_0 @ X0)
% 0.37/0.61          | ~ (l1_struct_0 @ X0)
% 0.37/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['17', '23'])).
% 0.37/0.61  thf('25', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.61  thf('26', plain,
% 0.37/0.61      (![X6 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('27', plain,
% 0.37/0.61      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('28', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('29', plain,
% 0.37/0.61      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.61      inference('demod', [status(thm)], ['27', '28'])).
% 0.37/0.61  thf('30', plain,
% 0.37/0.61      (((v13_waybel_0 @ sk_B @ 
% 0.37/0.61         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup+', [status(thm)], ['26', '29'])).
% 0.37/0.61  thf('31', plain,
% 0.37/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | (v13_waybel_0 @ sk_B @ 
% 0.37/0.61           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['25', '30'])).
% 0.37/0.61  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('33', plain,
% 0.37/0.61      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.61      inference('demod', [status(thm)], ['31', '32'])).
% 0.37/0.61  thf('34', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.61  thf('35', plain,
% 0.37/0.61      (![X6 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('36', plain,
% 0.37/0.61      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('37', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('38', plain,
% 0.37/0.61      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.61      inference('demod', [status(thm)], ['36', '37'])).
% 0.37/0.61  thf('39', plain,
% 0.37/0.61      (((v2_waybel_0 @ sk_B @ 
% 0.37/0.61         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup+', [status(thm)], ['35', '38'])).
% 0.37/0.61  thf('40', plain,
% 0.37/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | (v2_waybel_0 @ sk_B @ 
% 0.37/0.61           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['34', '39'])).
% 0.37/0.61  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('42', plain,
% 0.37/0.61      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.61      inference('demod', [status(thm)], ['40', '41'])).
% 0.37/0.61  thf('43', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.61  thf('44', plain,
% 0.37/0.61      (![X6 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('45', plain,
% 0.37/0.61      ((v1_subset_1 @ sk_B @ 
% 0.37/0.61        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('46', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('47', plain,
% 0.37/0.61      ((v1_subset_1 @ sk_B @ 
% 0.37/0.61        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.37/0.61      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.61  thf('48', plain,
% 0.37/0.61      (((v1_subset_1 @ sk_B @ 
% 0.37/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup+', [status(thm)], ['44', '47'])).
% 0.37/0.61  thf('49', plain,
% 0.37/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | (v1_subset_1 @ sk_B @ 
% 0.37/0.61           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['43', '48'])).
% 0.37/0.61  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('51', plain,
% 0.37/0.61      ((v1_subset_1 @ sk_B @ 
% 0.37/0.61        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.61      inference('demod', [status(thm)], ['49', '50'])).
% 0.37/0.61  thf('52', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61          | (v1_xboole_0 @ sk_B)
% 0.37/0.61          | (v2_struct_0 @ X0)
% 0.37/0.61          | ~ (l1_struct_0 @ X0)
% 0.37/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.61      inference('demod', [status(thm)], ['24', '33', '42', '51'])).
% 0.37/0.61  thf('53', plain,
% 0.37/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.61        | (v2_struct_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B)
% 0.37/0.61        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['8', '52'])).
% 0.37/0.61  thf('54', plain,
% 0.37/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61        | (v1_xboole_0 @ sk_B)
% 0.37/0.61        | (v2_struct_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['4', '53'])).
% 0.37/0.61  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('56', plain,
% 0.37/0.61      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61        | (v1_xboole_0 @ sk_B)
% 0.37/0.61        | (v2_struct_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('demod', [status(thm)], ['54', '55'])).
% 0.37/0.61  thf('57', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.61  thf('58', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.61  thf('59', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.37/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.61  thf(fc4_yellow19, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.37/0.61         ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.37/0.61         ( ~( v1_xboole_0 @ C ) ) & 
% 0.37/0.61         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.37/0.61         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.37/0.61         ( m1_subset_1 @
% 0.37/0.61           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.37/0.61       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.37/0.61         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.37/0.61         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.37/0.61         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.37/0.61  thf('60', plain,
% 0.37/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.37/0.61          | (v1_xboole_0 @ X13)
% 0.37/0.61          | ~ (l1_struct_0 @ X14)
% 0.37/0.61          | (v2_struct_0 @ X14)
% 0.37/0.61          | (v1_xboole_0 @ X15)
% 0.37/0.61          | ~ (v2_waybel_0 @ X15 @ (k3_yellow_1 @ X13))
% 0.37/0.61          | ~ (v13_waybel_0 @ X15 @ (k3_yellow_1 @ X13))
% 0.37/0.61          | ~ (m1_subset_1 @ X15 @ 
% 0.37/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X13))))
% 0.37/0.61          | (v4_orders_2 @ (k3_yellow19 @ X14 @ X13 @ X15)))),
% 0.37/0.61      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.37/0.61  thf('61', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('62', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('63', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('64', plain,
% 0.37/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.37/0.61          | (v1_xboole_0 @ X13)
% 0.37/0.61          | ~ (l1_struct_0 @ X14)
% 0.37/0.61          | (v2_struct_0 @ X14)
% 0.37/0.61          | (v1_xboole_0 @ X15)
% 0.37/0.61          | ~ (v2_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.37/0.61          | ~ (v13_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.37/0.61          | ~ (m1_subset_1 @ X15 @ 
% 0.37/0.61               (k1_zfmisc_1 @ 
% 0.37/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X13)))))
% 0.37/0.61          | (v4_orders_2 @ (k3_yellow19 @ X14 @ X13 @ X15)))),
% 0.37/0.61      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.37/0.61  thf('65', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61          | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.61          | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.61          | (v1_xboole_0 @ sk_B)
% 0.37/0.61          | (v2_struct_0 @ X0)
% 0.37/0.61          | ~ (l1_struct_0 @ X0)
% 0.37/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['59', '64'])).
% 0.37/0.61  thf('66', plain,
% 0.37/0.61      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.61      inference('demod', [status(thm)], ['31', '32'])).
% 0.37/0.61  thf('67', plain,
% 0.37/0.61      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.61      inference('demod', [status(thm)], ['40', '41'])).
% 0.37/0.61  thf('68', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61          | (v1_xboole_0 @ sk_B)
% 0.37/0.61          | (v2_struct_0 @ X0)
% 0.37/0.61          | ~ (l1_struct_0 @ X0)
% 0.37/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.61      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.37/0.61  thf('69', plain,
% 0.37/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.61        | (v2_struct_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B)
% 0.37/0.61        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['58', '68'])).
% 0.37/0.61  thf('70', plain,
% 0.37/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61        | (v1_xboole_0 @ sk_B)
% 0.37/0.61        | (v2_struct_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['57', '69'])).
% 0.37/0.61  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('72', plain,
% 0.37/0.61      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61        | (v1_xboole_0 @ sk_B)
% 0.37/0.61        | (v2_struct_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('demod', [status(thm)], ['70', '71'])).
% 0.37/0.61  thf('73', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.61  thf('74', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.61  thf('75', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.37/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.61  thf(dt_k3_yellow19, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.37/0.61         ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.37/0.61         ( ~( v1_xboole_0 @ C ) ) & 
% 0.37/0.61         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.37/0.61         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.37/0.61         ( m1_subset_1 @
% 0.37/0.61           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.37/0.61       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.37/0.61         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.37/0.61         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.37/0.61  thf('76', plain,
% 0.37/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.61          | (v1_xboole_0 @ X10)
% 0.37/0.61          | ~ (l1_struct_0 @ X11)
% 0.37/0.61          | (v2_struct_0 @ X11)
% 0.37/0.61          | (v1_xboole_0 @ X12)
% 0.37/0.61          | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.37/0.61          | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.37/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.37/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X10))))
% 0.37/0.61          | (l1_waybel_0 @ (k3_yellow19 @ X11 @ X10 @ X12) @ X11))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.37/0.61  thf('77', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('78', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('79', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('80', plain,
% 0.37/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.61          | (v1_xboole_0 @ X10)
% 0.37/0.61          | ~ (l1_struct_0 @ X11)
% 0.37/0.61          | (v2_struct_0 @ X11)
% 0.37/0.61          | (v1_xboole_0 @ X12)
% 0.37/0.61          | ~ (v2_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.37/0.61          | ~ (v13_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.37/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.37/0.61               (k1_zfmisc_1 @ 
% 0.37/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X10)))))
% 0.37/0.61          | (l1_waybel_0 @ (k3_yellow19 @ X11 @ X10 @ X12) @ X11))),
% 0.37/0.61      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 0.37/0.61  thf('81', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.61          | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.61          | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.61          | (v1_xboole_0 @ sk_B)
% 0.37/0.61          | (v2_struct_0 @ X0)
% 0.37/0.61          | ~ (l1_struct_0 @ X0)
% 0.37/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['75', '80'])).
% 0.37/0.61  thf('82', plain,
% 0.37/0.61      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.61      inference('demod', [status(thm)], ['31', '32'])).
% 0.37/0.61  thf('83', plain,
% 0.37/0.61      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.61      inference('demod', [status(thm)], ['40', '41'])).
% 0.37/0.61  thf('84', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.61          | (v1_xboole_0 @ sk_B)
% 0.37/0.61          | (v2_struct_0 @ X0)
% 0.37/0.61          | ~ (l1_struct_0 @ X0)
% 0.37/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.61      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.37/0.61  thf('85', plain,
% 0.37/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.61        | (v2_struct_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B)
% 0.37/0.61        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.61           sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['74', '84'])).
% 0.37/0.61  thf('86', plain,
% 0.37/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.61           sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B)
% 0.37/0.61        | (v2_struct_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['73', '85'])).
% 0.37/0.61  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('88', plain,
% 0.37/0.61      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.61         sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B)
% 0.37/0.61        | (v2_struct_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('demod', [status(thm)], ['86', '87'])).
% 0.37/0.61  thf('89', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.61  thf('90', plain,
% 0.37/0.61      (![X6 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('91', plain,
% 0.37/0.61      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.37/0.61        | (r3_waybel_9 @ sk_A @ 
% 0.37/0.61           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('92', plain,
% 0.37/0.61      (((r3_waybel_9 @ sk_A @ 
% 0.37/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.37/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('split', [status(esa)], ['91'])).
% 0.37/0.61  thf('93', plain,
% 0.37/0.61      ((((r3_waybel_9 @ sk_A @ 
% 0.37/0.61          (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.37/0.61         | ~ (l1_struct_0 @ sk_A)))
% 0.37/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('sup+', [status(thm)], ['90', '92'])).
% 0.37/0.61  thf('94', plain,
% 0.37/0.61      (((~ (l1_pre_topc @ sk_A)
% 0.37/0.61         | (r3_waybel_9 @ sk_A @ 
% 0.37/0.61            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C)))
% 0.37/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['89', '93'])).
% 0.37/0.61  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('96', plain,
% 0.37/0.61      (((r3_waybel_9 @ sk_A @ 
% 0.37/0.61         (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.37/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('demod', [status(thm)], ['94', '95'])).
% 0.37/0.61  thf('97', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(t12_yellow19, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.37/0.61             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.37/0.61           ( ![C:$i]:
% 0.37/0.61             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.61               ( ( r3_waybel_9 @ A @ B @ C ) <=>
% 0.37/0.61                 ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.37/0.61  thf('98', plain,
% 0.37/0.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.61         ((v2_struct_0 @ X19)
% 0.37/0.61          | ~ (v4_orders_2 @ X19)
% 0.37/0.61          | ~ (v7_waybel_0 @ X19)
% 0.37/0.61          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.37/0.61          | ~ (r3_waybel_9 @ X20 @ X19 @ X21)
% 0.37/0.61          | (r1_waybel_7 @ X20 @ (k2_yellow19 @ X20 @ X19) @ X21)
% 0.37/0.61          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.37/0.61          | ~ (l1_pre_topc @ X20)
% 0.37/0.61          | ~ (v2_pre_topc @ X20)
% 0.37/0.61          | (v2_struct_0 @ X20))),
% 0.37/0.61      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.37/0.61  thf('99', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v2_struct_0 @ sk_A)
% 0.37/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.61          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.37/0.61          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.37/0.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.37/0.61          | ~ (v7_waybel_0 @ X0)
% 0.37/0.61          | ~ (v4_orders_2 @ X0)
% 0.37/0.61          | (v2_struct_0 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['97', '98'])).
% 0.37/0.61  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('102', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v2_struct_0 @ sk_A)
% 0.37/0.61          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.37/0.61          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.37/0.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.37/0.61          | ~ (v7_waybel_0 @ X0)
% 0.37/0.61          | ~ (v4_orders_2 @ X0)
% 0.37/0.61          | (v2_struct_0 @ X0))),
% 0.37/0.61      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.37/0.61  thf('103', plain,
% 0.37/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61         | ~ (l1_waybel_0 @ 
% 0.37/0.61              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.37/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.37/0.61            (k2_yellow19 @ sk_A @ 
% 0.37/0.61             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.37/0.61            sk_C)
% 0.37/0.61         | (v2_struct_0 @ sk_A)))
% 0.37/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['96', '102'])).
% 0.37/0.61  thf('104', plain,
% 0.37/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61         | (v2_struct_0 @ sk_A)
% 0.37/0.61         | (v1_xboole_0 @ sk_B)
% 0.37/0.61         | (v2_struct_0 @ sk_A)
% 0.37/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.37/0.61            (k2_yellow19 @ sk_A @ 
% 0.37/0.61             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.37/0.61            sk_C)
% 0.37/0.61         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['88', '103'])).
% 0.37/0.61  thf('105', plain,
% 0.37/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.37/0.61            (k2_yellow19 @ sk_A @ 
% 0.37/0.61             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.37/0.61            sk_C)
% 0.37/0.61         | (v1_xboole_0 @ sk_B)
% 0.37/0.61         | (v2_struct_0 @ sk_A)
% 0.37/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['104'])).
% 0.37/0.61  thf('106', plain,
% 0.37/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61         | (v2_struct_0 @ sk_A)
% 0.37/0.61         | (v1_xboole_0 @ sk_B)
% 0.37/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61         | (v2_struct_0 @ sk_A)
% 0.37/0.61         | (v1_xboole_0 @ sk_B)
% 0.37/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.37/0.61            (k2_yellow19 @ sk_A @ 
% 0.37/0.61             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.37/0.61            sk_C)
% 0.37/0.61         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['72', '105'])).
% 0.37/0.61  thf('107', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.61  thf('108', plain,
% 0.37/0.61      (![X6 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('109', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.61  thf('110', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.37/0.61      inference('demod', [status(thm)], ['11', '12'])).
% 0.37/0.61  thf(t15_yellow19, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.61             ( v1_subset_1 @
% 0.37/0.61               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.37/0.61             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.61             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.61             ( m1_subset_1 @
% 0.37/0.61               B @ 
% 0.37/0.61               ( k1_zfmisc_1 @
% 0.37/0.61                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.37/0.61           ( ( B ) =
% 0.37/0.61             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.37/0.61  thf('111', plain,
% 0.37/0.61      (![X22 : $i, X23 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X22)
% 0.37/0.61          | ~ (v1_subset_1 @ X22 @ 
% 0.37/0.61               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X23))))
% 0.37/0.61          | ~ (v2_waybel_0 @ X22 @ (k3_yellow_1 @ (k2_struct_0 @ X23)))
% 0.37/0.61          | ~ (v13_waybel_0 @ X22 @ (k3_yellow_1 @ (k2_struct_0 @ X23)))
% 0.37/0.61          | ~ (m1_subset_1 @ X22 @ 
% 0.37/0.61               (k1_zfmisc_1 @ 
% 0.37/0.61                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X23)))))
% 0.37/0.61          | ((X22)
% 0.37/0.61              = (k2_yellow19 @ X23 @ 
% 0.37/0.61                 (k3_yellow19 @ X23 @ (k2_struct_0 @ X23) @ X22)))
% 0.37/0.61          | ~ (l1_struct_0 @ X23)
% 0.37/0.61          | (v2_struct_0 @ X23))),
% 0.37/0.61      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.37/0.61  thf('112', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('113', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('114', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('115', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('116', plain,
% 0.37/0.61      (![X22 : $i, X23 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X22)
% 0.37/0.61          | ~ (v1_subset_1 @ X22 @ 
% 0.37/0.61               (u1_struct_0 @ 
% 0.37/0.61                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X23)))))
% 0.37/0.61          | ~ (v2_waybel_0 @ X22 @ 
% 0.37/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X23))))
% 0.37/0.61          | ~ (v13_waybel_0 @ X22 @ 
% 0.37/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X23))))
% 0.37/0.61          | ~ (m1_subset_1 @ X22 @ 
% 0.37/0.61               (k1_zfmisc_1 @ 
% 0.37/0.61                (u1_struct_0 @ 
% 0.37/0.61                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X23))))))
% 0.37/0.61          | ((X22)
% 0.37/0.61              = (k2_yellow19 @ X23 @ 
% 0.37/0.61                 (k3_yellow19 @ X23 @ (k2_struct_0 @ X23) @ X22)))
% 0.37/0.61          | ~ (l1_struct_0 @ X23)
% 0.37/0.61          | (v2_struct_0 @ X23))),
% 0.37/0.61      inference('demod', [status(thm)], ['111', '112', '113', '114', '115'])).
% 0.37/0.61  thf('117', plain,
% 0.37/0.61      (((v2_struct_0 @ sk_A)
% 0.37/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.61        | ((sk_B)
% 0.37/0.61            = (k2_yellow19 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.61        | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.61             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.61        | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.61             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.61        | ~ (v1_subset_1 @ sk_B @ 
% 0.37/0.61             (u1_struct_0 @ 
% 0.37/0.61              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.37/0.61        | (v1_xboole_0 @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['110', '116'])).
% 0.37/0.61  thf('118', plain,
% 0.37/0.61      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.61      inference('demod', [status(thm)], ['27', '28'])).
% 0.37/0.61  thf('119', plain,
% 0.37/0.61      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.61      inference('demod', [status(thm)], ['36', '37'])).
% 0.37/0.61  thf('120', plain,
% 0.37/0.61      ((v1_subset_1 @ sk_B @ 
% 0.37/0.61        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.37/0.61      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.61  thf('121', plain,
% 0.37/0.61      (((v2_struct_0 @ sk_A)
% 0.37/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.61        | ((sk_B)
% 0.37/0.61            = (k2_yellow19 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.61        | (v1_xboole_0 @ sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 0.37/0.61  thf('122', plain,
% 0.37/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B)
% 0.37/0.61        | ((sk_B)
% 0.37/0.61            = (k2_yellow19 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.61        | (v2_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['109', '121'])).
% 0.37/0.61  thf('123', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('124', plain,
% 0.37/0.61      (((v1_xboole_0 @ sk_B)
% 0.37/0.61        | ((sk_B)
% 0.37/0.61            = (k2_yellow19 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.61        | (v2_struct_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['122', '123'])).
% 0.37/0.61  thf('125', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('126', plain,
% 0.37/0.61      (((v2_struct_0 @ sk_A)
% 0.37/0.61        | ((sk_B)
% 0.37/0.61            = (k2_yellow19 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.37/0.61      inference('clc', [status(thm)], ['124', '125'])).
% 0.37/0.61  thf('127', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('128', plain,
% 0.37/0.61      (((sk_B)
% 0.37/0.61         = (k2_yellow19 @ sk_A @ 
% 0.37/0.61            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.61      inference('clc', [status(thm)], ['126', '127'])).
% 0.37/0.61  thf('129', plain,
% 0.37/0.61      ((((sk_B)
% 0.37/0.61          = (k2_yellow19 @ sk_A @ 
% 0.37/0.61             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup+', [status(thm)], ['108', '128'])).
% 0.37/0.61  thf('130', plain,
% 0.37/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | ((sk_B)
% 0.37/0.61            = (k2_yellow19 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['107', '129'])).
% 0.37/0.61  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('132', plain,
% 0.37/0.61      (((sk_B)
% 0.37/0.61         = (k2_yellow19 @ sk_A @ 
% 0.37/0.61            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.61      inference('demod', [status(thm)], ['130', '131'])).
% 0.37/0.61  thf('133', plain,
% 0.37/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61         | (v2_struct_0 @ sk_A)
% 0.37/0.61         | (v1_xboole_0 @ sk_B)
% 0.37/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61         | (v2_struct_0 @ sk_A)
% 0.37/0.61         | (v1_xboole_0 @ sk_B)
% 0.37/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.37/0.61         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('demod', [status(thm)], ['106', '132'])).
% 0.37/0.61  thf('134', plain,
% 0.37/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.37/0.61         | (v1_xboole_0 @ sk_B)
% 0.37/0.61         | (v2_struct_0 @ sk_A)
% 0.37/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['133'])).
% 0.37/0.61  thf('135', plain,
% 0.37/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61         | (v2_struct_0 @ sk_A)
% 0.37/0.61         | (v1_xboole_0 @ sk_B)
% 0.37/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61         | (v2_struct_0 @ sk_A)
% 0.37/0.61         | (v1_xboole_0 @ sk_B)
% 0.37/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.37/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['56', '134'])).
% 0.37/0.61  thf('136', plain,
% 0.37/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.37/0.61         | (v1_xboole_0 @ sk_B)
% 0.37/0.61         | (v2_struct_0 @ sk_A)
% 0.37/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['135'])).
% 0.37/0.61  thf('137', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.61  thf('138', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B @ 
% 0.37/0.61        (k1_zfmisc_1 @ 
% 0.37/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.37/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.61  thf('139', plain,
% 0.37/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.61          | (v1_xboole_0 @ X10)
% 0.37/0.61          | ~ (l1_struct_0 @ X11)
% 0.37/0.61          | (v2_struct_0 @ X11)
% 0.37/0.61          | (v1_xboole_0 @ X12)
% 0.37/0.61          | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.37/0.61          | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.37/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.37/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X10))))
% 0.37/0.61          | ~ (v2_struct_0 @ (k3_yellow19 @ X11 @ X10 @ X12)))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.37/0.61  thf('140', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('141', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('142', plain,
% 0.37/0.61      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.61  thf('143', plain,
% 0.37/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.61          | (v1_xboole_0 @ X10)
% 0.37/0.61          | ~ (l1_struct_0 @ X11)
% 0.37/0.61          | (v2_struct_0 @ X11)
% 0.37/0.61          | (v1_xboole_0 @ X12)
% 0.37/0.61          | ~ (v2_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.37/0.61          | ~ (v13_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.37/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.37/0.61               (k1_zfmisc_1 @ 
% 0.37/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X10)))))
% 0.37/0.61          | ~ (v2_struct_0 @ (k3_yellow19 @ X11 @ X10 @ X12)))),
% 0.37/0.61      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 0.37/0.61  thf('144', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61          | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.61          | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.61          | (v1_xboole_0 @ sk_B)
% 0.37/0.61          | (v2_struct_0 @ X0)
% 0.37/0.61          | ~ (l1_struct_0 @ X0)
% 0.37/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['138', '143'])).
% 0.37/0.61  thf('145', plain,
% 0.37/0.61      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.61      inference('demod', [status(thm)], ['31', '32'])).
% 0.37/0.61  thf('146', plain,
% 0.37/0.61      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.61      inference('demod', [status(thm)], ['40', '41'])).
% 0.37/0.61  thf('147', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61          | (v1_xboole_0 @ sk_B)
% 0.37/0.61          | (v2_struct_0 @ X0)
% 0.37/0.61          | ~ (l1_struct_0 @ X0)
% 0.37/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.61      inference('demod', [status(thm)], ['144', '145', '146'])).
% 0.37/0.61  thf('148', plain,
% 0.37/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.61        | (v2_struct_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B)
% 0.37/0.61        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['137', '147'])).
% 0.37/0.61  thf('149', plain,
% 0.37/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61         | (v2_struct_0 @ sk_A)
% 0.37/0.61         | (v1_xboole_0 @ sk_B)
% 0.37/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.37/0.61         | (v1_xboole_0 @ sk_B)
% 0.37/0.61         | (v2_struct_0 @ sk_A)
% 0.37/0.61         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['136', '148'])).
% 0.37/0.61  thf('150', plain,
% 0.37/0.61      (((~ (l1_struct_0 @ sk_A)
% 0.37/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.37/0.61         | (v1_xboole_0 @ sk_B)
% 0.37/0.61         | (v2_struct_0 @ sk_A)
% 0.37/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['149'])).
% 0.37/0.61  thf('151', plain,
% 0.37/0.61      (((~ (l1_pre_topc @ sk_A)
% 0.37/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61         | (v2_struct_0 @ sk_A)
% 0.37/0.61         | (v1_xboole_0 @ sk_B)
% 0.37/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.37/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['3', '150'])).
% 0.37/0.61  thf('152', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('153', plain,
% 0.37/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61         | (v2_struct_0 @ sk_A)
% 0.37/0.61         | (v1_xboole_0 @ sk_B)
% 0.37/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.37/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('demod', [status(thm)], ['151', '152'])).
% 0.37/0.61  thf('154', plain,
% 0.37/0.61      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.37/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.61      inference('split', [status(esa)], ['0'])).
% 0.37/0.61  thf('155', plain,
% 0.37/0.61      ((((v1_xboole_0 @ sk_B)
% 0.37/0.61         | (v2_struct_0 @ sk_A)
% 0.37/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.37/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['153', '154'])).
% 0.37/0.61  thf('156', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('157', plain,
% 0.37/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.37/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.37/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('clc', [status(thm)], ['155', '156'])).
% 0.37/0.61  thf('158', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('159', plain,
% 0.37/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.37/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.37/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('clc', [status(thm)], ['157', '158'])).
% 0.37/0.61  thf('160', plain,
% 0.37/0.61      (![X6 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf(fc5_struct_0, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.61       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.37/0.61  thf('161', plain,
% 0.37/0.61      (![X8 : $i]:
% 0.37/0.61         (~ (v1_xboole_0 @ (k2_struct_0 @ X8))
% 0.37/0.61          | ~ (l1_struct_0 @ X8)
% 0.37/0.61          | (v2_struct_0 @ X8))),
% 0.37/0.61      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.37/0.61  thf('162', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.37/0.61          | ~ (l1_struct_0 @ X0)
% 0.37/0.61          | (v2_struct_0 @ X0)
% 0.37/0.61          | ~ (l1_struct_0 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['160', '161'])).
% 0.37/0.61  thf('163', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v2_struct_0 @ X0)
% 0.37/0.61          | ~ (l1_struct_0 @ X0)
% 0.37/0.61          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['162'])).
% 0.37/0.61  thf('164', plain,
% 0.37/0.61      (((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.37/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.37/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['159', '163'])).
% 0.37/0.61  thf('165', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('166', plain,
% 0.37/0.61      ((~ (l1_struct_0 @ sk_A))
% 0.37/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.37/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('clc', [status(thm)], ['164', '165'])).
% 0.37/0.61  thf('167', plain,
% 0.37/0.61      ((~ (l1_pre_topc @ sk_A))
% 0.37/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.37/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['2', '166'])).
% 0.37/0.61  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('169', plain,
% 0.37/0.61      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.37/0.61       ~
% 0.37/0.61       ((r3_waybel_9 @ sk_A @ 
% 0.37/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['167', '168'])).
% 0.37/0.61  thf('170', plain,
% 0.37/0.61      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.37/0.61       ((r3_waybel_9 @ sk_A @ 
% 0.37/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.37/0.61      inference('split', [status(esa)], ['91'])).
% 0.37/0.61  thf('171', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.61  thf('172', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.61  thf('173', plain,
% 0.37/0.61      (![X6 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('174', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.61  thf('175', plain,
% 0.37/0.61      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.37/0.61         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.61      inference('split', [status(esa)], ['91'])).
% 0.37/0.61  thf('176', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.61  thf('177', plain,
% 0.37/0.61      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61        | (v1_xboole_0 @ sk_B)
% 0.37/0.61        | (v2_struct_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('demod', [status(thm)], ['54', '55'])).
% 0.37/0.61  thf('178', plain,
% 0.37/0.61      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61        | (v1_xboole_0 @ sk_B)
% 0.37/0.61        | (v2_struct_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('demod', [status(thm)], ['70', '71'])).
% 0.37/0.61  thf('179', plain,
% 0.37/0.61      (![X6 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('180', plain,
% 0.37/0.61      (![X6 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('181', plain,
% 0.37/0.61      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.61         sk_A)
% 0.37/0.61        | (v1_xboole_0 @ sk_B)
% 0.37/0.61        | (v2_struct_0 @ sk_A)
% 0.37/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('demod', [status(thm)], ['86', '87'])).
% 0.37/0.61  thf('182', plain,
% 0.37/0.61      (![X6 : $i]:
% 0.37/0.61         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.61  thf('183', plain,
% 0.37/0.61      (((sk_B)
% 0.37/0.61         = (k2_yellow19 @ sk_A @ 
% 0.37/0.61            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.61      inference('clc', [status(thm)], ['126', '127'])).
% 0.37/0.61  thf('184', plain,
% 0.37/0.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.61         ((v2_struct_0 @ X19)
% 0.37/0.61          | ~ (v4_orders_2 @ X19)
% 0.37/0.61          | ~ (v7_waybel_0 @ X19)
% 0.37/0.61          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.37/0.61          | ~ (r1_waybel_7 @ X20 @ (k2_yellow19 @ X20 @ X19) @ X21)
% 0.37/0.61          | (r3_waybel_9 @ X20 @ X19 @ X21)
% 0.37/0.61          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.37/0.61          | ~ (l1_pre_topc @ X20)
% 0.37/0.61          | ~ (v2_pre_topc @ X20)
% 0.37/0.61          | (v2_struct_0 @ X20))),
% 0.37/0.61      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.37/0.61  thf('185', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.61          | (v2_struct_0 @ sk_A)
% 0.37/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.37/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.61          | ~ (l1_waybel_0 @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.37/0.61          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['183', '184'])).
% 0.37/0.61  thf('186', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('187', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('188', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.61          | (v2_struct_0 @ sk_A)
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.37/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.61          | ~ (l1_waybel_0 @ 
% 0.37/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.37/0.61          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.61      inference('demod', [status(thm)], ['185', '186', '187'])).
% 0.37/0.61  thf('189', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (l1_waybel_0 @ 
% 0.37/0.61             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.37/0.61          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.37/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61          | (v2_struct_0 @ sk_A)
% 0.37/0.61          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['182', '188'])).
% 0.37/0.61  thf('190', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61          | (v2_struct_0 @ sk_A)
% 0.37/0.61          | (v1_xboole_0 @ sk_B)
% 0.37/0.61          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.61          | (v2_struct_0 @ sk_A)
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.61          | (r3_waybel_9 @ sk_A @ 
% 0.37/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.61          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61          | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['181', '189'])).
% 0.37/0.61  thf('191', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (l1_struct_0 @ sk_A)
% 0.37/0.61          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.61          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62          | (r3_waybel_9 @ sk_A @ 
% 0.37/0.62             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.62          | (v1_xboole_0 @ sk_B)
% 0.37/0.62          | (v2_struct_0 @ sk_A)
% 0.37/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['190'])).
% 0.37/0.62  thf('192', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | (v2_struct_0 @ sk_A)
% 0.37/0.62          | (v1_xboole_0 @ sk_B)
% 0.37/0.62          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | (r3_waybel_9 @ sk_A @ 
% 0.37/0.62             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.62          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62          | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['180', '191'])).
% 0.37/0.62  thf('193', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62          | (r3_waybel_9 @ sk_A @ 
% 0.37/0.62             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.62          | (v1_xboole_0 @ sk_B)
% 0.37/0.62          | (v2_struct_0 @ sk_A)
% 0.37/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.62          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['192'])).
% 0.37/0.62  thf('194', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.62          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | (v2_struct_0 @ sk_A)
% 0.37/0.62          | (v1_xboole_0 @ sk_B)
% 0.37/0.62          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | (r3_waybel_9 @ sk_A @ 
% 0.37/0.62             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['179', '193'])).
% 0.37/0.62  thf('195', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62          | (r3_waybel_9 @ sk_A @ 
% 0.37/0.62             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.62          | (v1_xboole_0 @ sk_B)
% 0.37/0.62          | (v2_struct_0 @ sk_A)
% 0.37/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.62          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['194'])).
% 0.37/0.62  thf('196', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | (v2_struct_0 @ sk_A)
% 0.37/0.62          | (v1_xboole_0 @ sk_B)
% 0.37/0.62          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | (v2_struct_0 @ sk_A)
% 0.37/0.62          | (v1_xboole_0 @ sk_B)
% 0.37/0.62          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | (r3_waybel_9 @ sk_A @ 
% 0.37/0.62             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['178', '195'])).
% 0.37/0.62  thf('197', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62          | (r3_waybel_9 @ sk_A @ 
% 0.37/0.62             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.62          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.62          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62          | (v1_xboole_0 @ sk_B)
% 0.37/0.62          | (v2_struct_0 @ sk_A)
% 0.37/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['196'])).
% 0.37/0.62  thf('198', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | (v2_struct_0 @ sk_A)
% 0.37/0.62          | (v1_xboole_0 @ sk_B)
% 0.37/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | (v2_struct_0 @ sk_A)
% 0.37/0.62          | (v1_xboole_0 @ sk_B)
% 0.37/0.62          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.62          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | (r3_waybel_9 @ sk_A @ 
% 0.37/0.62             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['177', '197'])).
% 0.37/0.62  thf('199', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62          | (r3_waybel_9 @ sk_A @ 
% 0.37/0.62             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.62          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.62          | (v1_xboole_0 @ sk_B)
% 0.37/0.62          | (v2_struct_0 @ sk_A)
% 0.37/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['198'])).
% 0.37/0.62  thf('200', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (l1_pre_topc @ sk_A)
% 0.37/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | (v2_struct_0 @ sk_A)
% 0.37/0.62          | (v1_xboole_0 @ sk_B)
% 0.37/0.62          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | (r3_waybel_9 @ sk_A @ 
% 0.37/0.62             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['176', '199'])).
% 0.37/0.62  thf('201', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('202', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | (v2_struct_0 @ sk_A)
% 0.37/0.62          | (v1_xboole_0 @ sk_B)
% 0.37/0.62          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | (r3_waybel_9 @ sk_A @ 
% 0.37/0.62             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['200', '201'])).
% 0.37/0.62  thf('203', plain,
% 0.37/0.62      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62         | (r3_waybel_9 @ sk_A @ 
% 0.37/0.62            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.37/0.62         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.37/0.62         | (v1_xboole_0 @ sk_B)
% 0.37/0.62         | (v2_struct_0 @ sk_A)
% 0.37/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.62         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['175', '202'])).
% 0.37/0.62  thf('204', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('205', plain,
% 0.37/0.62      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62         | (r3_waybel_9 @ sk_A @ 
% 0.37/0.62            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.37/0.62         | (v1_xboole_0 @ sk_B)
% 0.37/0.62         | (v2_struct_0 @ sk_A)
% 0.37/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.62         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.62      inference('demod', [status(thm)], ['203', '204'])).
% 0.37/0.62  thf('206', plain,
% 0.37/0.62      ((~ (r3_waybel_9 @ sk_A @ 
% 0.37/0.62           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.37/0.62      inference('split', [status(esa)], ['0'])).
% 0.37/0.62  thf('207', plain,
% 0.37/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62         | (v2_struct_0 @ sk_A)
% 0.37/0.62         | (v1_xboole_0 @ sk_B)
% 0.37/0.62         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.37/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['205', '206'])).
% 0.37/0.62  thf('208', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.62  thf('209', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.62  thf('210', plain,
% 0.37/0.62      (![X6 : $i]:
% 0.37/0.62         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.37/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.62  thf('211', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_B @ 
% 0.37/0.62        (k1_zfmisc_1 @ 
% 0.37/0.62         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.37/0.62      inference('demod', [status(thm)], ['11', '12'])).
% 0.37/0.62  thf('212', plain,
% 0.37/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.62          | (v1_xboole_0 @ X10)
% 0.37/0.62          | ~ (l1_struct_0 @ X11)
% 0.37/0.62          | (v2_struct_0 @ X11)
% 0.37/0.62          | (v1_xboole_0 @ X12)
% 0.37/0.62          | ~ (v2_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.37/0.62          | ~ (v13_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.37/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.37/0.62               (k1_zfmisc_1 @ 
% 0.37/0.62                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X10)))))
% 0.37/0.62          | ~ (v2_struct_0 @ (k3_yellow19 @ X11 @ X10 @ X12)))),
% 0.37/0.62      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 0.37/0.62  thf('213', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62          | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.62               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.62          | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.62               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.62          | (v1_xboole_0 @ sk_B)
% 0.37/0.62          | (v2_struct_0 @ X0)
% 0.37/0.62          | ~ (l1_struct_0 @ X0)
% 0.37/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.62          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['211', '212'])).
% 0.37/0.62  thf('214', plain,
% 0.37/0.62      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.62        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.37/0.62  thf('215', plain,
% 0.37/0.62      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.62        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.62      inference('demod', [status(thm)], ['36', '37'])).
% 0.37/0.62  thf('216', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62          | (v1_xboole_0 @ sk_B)
% 0.37/0.62          | (v2_struct_0 @ X0)
% 0.37/0.62          | ~ (l1_struct_0 @ X0)
% 0.37/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.62          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.62      inference('demod', [status(thm)], ['213', '214', '215'])).
% 0.37/0.62  thf('217', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.37/0.62          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.62          | ~ (l1_struct_0 @ X0)
% 0.37/0.62          | (v2_struct_0 @ X0)
% 0.37/0.62          | (v1_xboole_0 @ sk_B)
% 0.37/0.62          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['210', '216'])).
% 0.37/0.62  thf('218', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (l1_pre_topc @ sk_A)
% 0.37/0.62          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62          | (v1_xboole_0 @ sk_B)
% 0.37/0.62          | (v2_struct_0 @ X0)
% 0.37/0.62          | ~ (l1_struct_0 @ X0)
% 0.37/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['209', '217'])).
% 0.37/0.62  thf('219', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('220', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.62          | (v1_xboole_0 @ sk_B)
% 0.37/0.62          | (v2_struct_0 @ X0)
% 0.37/0.62          | ~ (l1_struct_0 @ X0)
% 0.37/0.62          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.62          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.62               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.62      inference('demod', [status(thm)], ['218', '219'])).
% 0.37/0.62  thf('221', plain,
% 0.37/0.62      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.62        | (v2_struct_0 @ sk_A)
% 0.37/0.62        | (v1_xboole_0 @ sk_B)
% 0.37/0.62        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['208', '220'])).
% 0.37/0.62  thf('222', plain,
% 0.37/0.62      ((((v1_xboole_0 @ sk_B)
% 0.37/0.62         | (v2_struct_0 @ sk_A)
% 0.37/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62         | (v1_xboole_0 @ sk_B)
% 0.37/0.62         | (v2_struct_0 @ sk_A)
% 0.37/0.62         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.62         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.37/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['207', '221'])).
% 0.37/0.62  thf('223', plain,
% 0.37/0.62      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.62         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62         | (v2_struct_0 @ sk_A)
% 0.37/0.62         | (v1_xboole_0 @ sk_B)))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.37/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['222'])).
% 0.37/0.62  thf('224', plain,
% 0.37/0.62      (((~ (l1_pre_topc @ sk_A)
% 0.37/0.62         | (v1_xboole_0 @ sk_B)
% 0.37/0.62         | (v2_struct_0 @ sk_A)
% 0.37/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.37/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['174', '223'])).
% 0.37/0.62  thf('225', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('226', plain,
% 0.37/0.62      ((((v1_xboole_0 @ sk_B)
% 0.37/0.62         | (v2_struct_0 @ sk_A)
% 0.37/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.37/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.62      inference('demod', [status(thm)], ['224', '225'])).
% 0.37/0.62  thf('227', plain,
% 0.37/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62         | (v2_struct_0 @ sk_A)
% 0.37/0.62         | (v1_xboole_0 @ sk_B)))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.37/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['173', '226'])).
% 0.37/0.62  thf('228', plain,
% 0.37/0.62      ((((v1_xboole_0 @ sk_B)
% 0.37/0.62         | (v2_struct_0 @ sk_A)
% 0.37/0.62         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.37/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['227'])).
% 0.37/0.62  thf('229', plain,
% 0.37/0.62      (((~ (l1_pre_topc @ sk_A)
% 0.37/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62         | (v2_struct_0 @ sk_A)
% 0.37/0.62         | (v1_xboole_0 @ sk_B)))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.37/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['172', '228'])).
% 0.37/0.62  thf('230', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('231', plain,
% 0.37/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62         | (v2_struct_0 @ sk_A)
% 0.37/0.62         | (v1_xboole_0 @ sk_B)))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.37/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.62      inference('demod', [status(thm)], ['229', '230'])).
% 0.37/0.62  thf('232', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('233', plain,
% 0.37/0.62      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.37/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.62      inference('clc', [status(thm)], ['231', '232'])).
% 0.37/0.62  thf('234', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('235', plain,
% 0.37/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.37/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.62      inference('clc', [status(thm)], ['233', '234'])).
% 0.37/0.62  thf('236', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ X0)
% 0.37/0.62          | ~ (l1_struct_0 @ X0)
% 0.37/0.62          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['162'])).
% 0.37/0.62  thf('237', plain,
% 0.37/0.62      (((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.37/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['235', '236'])).
% 0.37/0.62  thf('238', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('239', plain,
% 0.37/0.62      ((~ (l1_struct_0 @ sk_A))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.37/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.62      inference('clc', [status(thm)], ['237', '238'])).
% 0.37/0.62  thf('240', plain,
% 0.37/0.62      ((~ (l1_pre_topc @ sk_A))
% 0.37/0.62         <= (~
% 0.37/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.37/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.37/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['171', '239'])).
% 0.37/0.62  thf('241', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('242', plain,
% 0.37/0.62      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.37/0.62       ((r3_waybel_9 @ sk_A @ 
% 0.37/0.62         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.37/0.62      inference('demod', [status(thm)], ['240', '241'])).
% 0.37/0.62  thf('243', plain, ($false),
% 0.37/0.62      inference('sat_resolution*', [status(thm)], ['1', '169', '170', '242'])).
% 0.37/0.62  
% 0.37/0.62  % SZS output end Refutation
% 0.37/0.62  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
