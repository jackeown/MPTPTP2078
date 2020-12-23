%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qQovoEQwNH

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:53 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  284 ( 905 expanded)
%              Number of leaves         :   41 ( 295 expanded)
%              Depth                    :   42
%              Number of atoms          : 3812 (16277 expanded)
%              Number of equality atoms :   50 ( 237 expanded)
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

thf('158',plain,(
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

thf('159',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['157','161'])).

thf('163',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['2','164'])).

thf('166',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['91'])).

thf('169',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('170',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('171',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('172',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('173',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['91'])).

thf('174',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('175',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('176',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('177',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('178',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('179',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('180',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('181',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('182',plain,(
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

thf('183',plain,(
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
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,(
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
    inference('sup-',[status(thm)],['180','186'])).

thf('188',plain,(
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
    inference('sup-',[status(thm)],['179','187'])).

thf('189',plain,(
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
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,(
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
    inference('sup-',[status(thm)],['178','189'])).

thf('191',plain,(
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
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
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
    inference('sup-',[status(thm)],['177','191'])).

thf('193',plain,(
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
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
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
    inference('sup-',[status(thm)],['176','193'])).

thf('195',plain,(
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
    inference(simplify,[status(thm)],['194'])).

thf('196',plain,(
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
    inference('sup-',[status(thm)],['175','195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['174','197'])).

thf('199',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['173','200'])).

thf('202',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('205',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('207',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('208',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('209',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('210',plain,(
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

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('213',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['211','212','213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['208','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['207','215'])).

thf('217',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['206','218'])).

thf('220',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['205','219'])).

thf('221',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['172','221'])).

thf('223',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['171','224'])).

thf('226',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['170','226'])).

thf('228',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['229','230'])).

thf('232',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('235',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['235','236'])).

thf('238',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['169','237'])).

thf('239',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['238','239'])).

thf('241',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','167','168','240'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qQovoEQwNH
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 189 iterations in 0.099s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.57  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.38/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.57  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.38/0.57  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.38/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.38/0.57  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.38/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.57  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.38/0.57  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.38/0.57  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.38/0.57  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.38/0.57  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.38/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.57  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.38/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.57  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.57  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.38/0.57  thf(r2_waybel_7_type, type, r2_waybel_7: $i > $i > $i > $o).
% 0.38/0.57  thf(t18_yellow19, conjecture,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.57             ( v1_subset_1 @
% 0.38/0.57               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.38/0.57             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.57             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.57             ( m1_subset_1 @
% 0.38/0.57               B @ 
% 0.38/0.57               ( k1_zfmisc_1 @
% 0.38/0.57                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.38/0.57           ( ![C:$i]:
% 0.38/0.57             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.57               ( ( r2_hidden @
% 0.38/0.57                   C @ 
% 0.38/0.57                   ( k10_yellow_6 @
% 0.38/0.57                     A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) <=>
% 0.38/0.57                 ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i]:
% 0.38/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.57            ( l1_pre_topc @ A ) ) =>
% 0.38/0.57          ( ![B:$i]:
% 0.38/0.57            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.57                ( v1_subset_1 @
% 0.38/0.57                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.38/0.57                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.57                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.57                ( m1_subset_1 @
% 0.38/0.57                  B @ 
% 0.38/0.57                  ( k1_zfmisc_1 @
% 0.38/0.57                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.38/0.57              ( ![C:$i]:
% 0.38/0.57                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.57                  ( ( r2_hidden @
% 0.38/0.57                      C @ 
% 0.38/0.57                      ( k10_yellow_6 @
% 0.38/0.57                        A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) <=>
% 0.38/0.57                    ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t18_yellow19])).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      ((~ (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.57        | ~ (r2_hidden @ sk_C @ 
% 0.38/0.57             (k10_yellow_6 @ sk_A @ 
% 0.38/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.38/0.57       ~
% 0.38/0.57       ((r2_hidden @ sk_C @ 
% 0.38/0.57         (k10_yellow_6 @ sk_A @ 
% 0.38/0.57          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.38/0.57      inference('split', [status(esa)], ['0'])).
% 0.38/0.57  thf(dt_l1_pre_topc, axiom,
% 0.38/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.57  thf('2', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf('3', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf('4', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf(d10_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.57  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.57      inference('simplify', [status(thm)], ['5'])).
% 0.38/0.57  thf(t3_subset, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X3 : $i, X5 : $i]:
% 0.38/0.57         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.38/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.57  thf('8', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.57  thf('9', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf(d3_struct_0, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      (![X6 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ 
% 0.38/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(d2_yellow_1, axiom,
% 0.38/0.57    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (((m1_subset_1 @ sk_B @ 
% 0.38/0.57         (k1_zfmisc_1 @ 
% 0.38/0.57          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.57      inference('sup+', [status(thm)], ['10', '13'])).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | (m1_subset_1 @ sk_B @ 
% 0.38/0.57           (k1_zfmisc_1 @ 
% 0.38/0.57            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['9', '14'])).
% 0.38/0.57  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.38/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.57  thf(fc4_yellow19, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.38/0.57         ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.38/0.57         ( ~( v1_xboole_0 @ C ) ) & 
% 0.38/0.57         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.38/0.57         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.38/0.57         ( m1_subset_1 @
% 0.38/0.57           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.38/0.57       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.38/0.57         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.38/0.57         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.38/0.57         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.38/0.57          | (v1_xboole_0 @ X13)
% 0.38/0.57          | ~ (l1_struct_0 @ X14)
% 0.38/0.57          | (v2_struct_0 @ X14)
% 0.38/0.57          | (v1_xboole_0 @ X15)
% 0.38/0.57          | ~ (v2_waybel_0 @ X15 @ (k3_yellow_1 @ X13))
% 0.38/0.57          | ~ (v13_waybel_0 @ X15 @ (k3_yellow_1 @ X13))
% 0.38/0.57          | ~ (m1_subset_1 @ X15 @ 
% 0.38/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X13))))
% 0.38/0.57          | (v4_orders_2 @ (k3_yellow19 @ X14 @ X13 @ X15)))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.38/0.57          | (v1_xboole_0 @ X13)
% 0.38/0.57          | ~ (l1_struct_0 @ X14)
% 0.38/0.57          | (v2_struct_0 @ X14)
% 0.38/0.57          | (v1_xboole_0 @ X15)
% 0.38/0.57          | ~ (v2_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.38/0.57          | ~ (v13_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.38/0.57          | ~ (m1_subset_1 @ X15 @ 
% 0.38/0.57               (k1_zfmisc_1 @ 
% 0.38/0.57                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X13)))))
% 0.38/0.57          | (v4_orders_2 @ (k3_yellow19 @ X14 @ X13 @ X15)))),
% 0.38/0.57      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | ~ (v13_waybel_0 @ sk_B @ 
% 0.38/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57          | ~ (v2_waybel_0 @ sk_B @ 
% 0.38/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | (v2_struct_0 @ X0)
% 0.38/0.57          | ~ (l1_struct_0 @ X0)
% 0.38/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['17', '22'])).
% 0.38/0.57  thf('24', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X6 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (((v13_waybel_0 @ sk_B @ 
% 0.38/0.57         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.57      inference('sup+', [status(thm)], ['25', '28'])).
% 0.38/0.57  thf('30', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | (v13_waybel_0 @ sk_B @ 
% 0.38/0.57           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['24', '29'])).
% 0.38/0.57  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['30', '31'])).
% 0.38/0.57  thf('33', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf('34', plain,
% 0.38/0.57      (![X6 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('37', plain,
% 0.38/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      (((v2_waybel_0 @ sk_B @ 
% 0.38/0.57         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.57      inference('sup+', [status(thm)], ['34', '37'])).
% 0.38/0.57  thf('39', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | (v2_waybel_0 @ sk_B @ 
% 0.38/0.57           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['33', '38'])).
% 0.38/0.57  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.38/0.57  thf('42', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | (v2_struct_0 @ X0)
% 0.38/0.57          | ~ (l1_struct_0 @ X0)
% 0.38/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.57      inference('demod', [status(thm)], ['23', '32', '41'])).
% 0.38/0.57  thf('43', plain,
% 0.38/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57        | (v2_struct_0 @ sk_A)
% 0.38/0.57        | (v1_xboole_0 @ sk_B)
% 0.38/0.57        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['8', '42'])).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57        | (v1_xboole_0 @ sk_B)
% 0.38/0.57        | (v2_struct_0 @ sk_A)
% 0.38/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['4', '43'])).
% 0.38/0.57  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('46', plain,
% 0.38/0.57      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57        | (v1_xboole_0 @ sk_B)
% 0.38/0.57        | (v2_struct_0 @ sk_A)
% 0.38/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['44', '45'])).
% 0.38/0.57  thf('47', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf('48', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.57  thf('49', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.38/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.57  thf(fc5_yellow19, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.38/0.57         ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.38/0.57         ( ~( v1_xboole_0 @ C ) ) & 
% 0.38/0.57         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.38/0.57         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.38/0.57         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.38/0.57         ( m1_subset_1 @
% 0.38/0.57           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.38/0.57       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.38/0.57         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.38/0.57         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.38/0.57  thf('50', plain,
% 0.38/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.38/0.57          | (v1_xboole_0 @ X16)
% 0.38/0.57          | ~ (l1_struct_0 @ X17)
% 0.38/0.57          | (v2_struct_0 @ X17)
% 0.38/0.57          | (v1_xboole_0 @ X18)
% 0.38/0.57          | ~ (v1_subset_1 @ X18 @ (u1_struct_0 @ (k3_yellow_1 @ X16)))
% 0.38/0.57          | ~ (v2_waybel_0 @ X18 @ (k3_yellow_1 @ X16))
% 0.38/0.57          | ~ (v13_waybel_0 @ X18 @ (k3_yellow_1 @ X16))
% 0.38/0.57          | ~ (m1_subset_1 @ X18 @ 
% 0.38/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X16))))
% 0.38/0.57          | (v7_waybel_0 @ (k3_yellow19 @ X17 @ X16 @ X18)))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.38/0.57  thf('51', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('52', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('53', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('54', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('55', plain,
% 0.38/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.38/0.57          | (v1_xboole_0 @ X16)
% 0.38/0.57          | ~ (l1_struct_0 @ X17)
% 0.38/0.57          | (v2_struct_0 @ X17)
% 0.38/0.57          | (v1_xboole_0 @ X18)
% 0.38/0.57          | ~ (v1_subset_1 @ X18 @ 
% 0.38/0.57               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X16))))
% 0.38/0.57          | ~ (v2_waybel_0 @ X18 @ (k3_lattice3 @ (k1_lattice3 @ X16)))
% 0.38/0.57          | ~ (v13_waybel_0 @ X18 @ (k3_lattice3 @ (k1_lattice3 @ X16)))
% 0.38/0.57          | ~ (m1_subset_1 @ X18 @ 
% 0.38/0.57               (k1_zfmisc_1 @ 
% 0.38/0.57                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X16)))))
% 0.38/0.57          | (v7_waybel_0 @ (k3_yellow19 @ X17 @ X16 @ X18)))),
% 0.38/0.57      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.38/0.57  thf('56', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | ~ (v13_waybel_0 @ sk_B @ 
% 0.38/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57          | ~ (v2_waybel_0 @ sk_B @ 
% 0.38/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57          | ~ (v1_subset_1 @ sk_B @ 
% 0.38/0.57               (u1_struct_0 @ 
% 0.38/0.57                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | (v2_struct_0 @ X0)
% 0.38/0.57          | ~ (l1_struct_0 @ X0)
% 0.38/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['49', '55'])).
% 0.38/0.57  thf('57', plain,
% 0.38/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['30', '31'])).
% 0.38/0.57  thf('58', plain,
% 0.38/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.38/0.57  thf('59', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf('60', plain,
% 0.38/0.57      (![X6 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('61', plain,
% 0.38/0.57      ((v1_subset_1 @ sk_B @ 
% 0.38/0.57        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('62', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('63', plain,
% 0.38/0.57      ((v1_subset_1 @ sk_B @ 
% 0.38/0.57        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.38/0.57      inference('demod', [status(thm)], ['61', '62'])).
% 0.38/0.57  thf('64', plain,
% 0.38/0.57      (((v1_subset_1 @ sk_B @ 
% 0.38/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.57      inference('sup+', [status(thm)], ['60', '63'])).
% 0.38/0.57  thf('65', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | (v1_subset_1 @ sk_B @ 
% 0.38/0.57           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['59', '64'])).
% 0.38/0.57  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('67', plain,
% 0.38/0.57      ((v1_subset_1 @ sk_B @ 
% 0.38/0.57        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.38/0.57      inference('demod', [status(thm)], ['65', '66'])).
% 0.38/0.57  thf('68', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | (v2_struct_0 @ X0)
% 0.38/0.57          | ~ (l1_struct_0 @ X0)
% 0.38/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.57      inference('demod', [status(thm)], ['56', '57', '58', '67'])).
% 0.38/0.57  thf('69', plain,
% 0.38/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57        | (v2_struct_0 @ sk_A)
% 0.38/0.57        | (v1_xboole_0 @ sk_B)
% 0.38/0.57        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['48', '68'])).
% 0.38/0.57  thf('70', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57        | (v1_xboole_0 @ sk_B)
% 0.38/0.57        | (v2_struct_0 @ sk_A)
% 0.38/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['47', '69'])).
% 0.38/0.57  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('72', plain,
% 0.38/0.57      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57        | (v1_xboole_0 @ sk_B)
% 0.38/0.57        | (v2_struct_0 @ sk_A)
% 0.38/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['70', '71'])).
% 0.38/0.57  thf('73', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf('74', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.57  thf('75', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.38/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.57  thf(dt_k3_yellow19, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.38/0.57         ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.38/0.57         ( ~( v1_xboole_0 @ C ) ) & 
% 0.38/0.57         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.38/0.57         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.38/0.57         ( m1_subset_1 @
% 0.38/0.57           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.38/0.57       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.38/0.57         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.38/0.57         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.38/0.57  thf('76', plain,
% 0.38/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.38/0.57          | (v1_xboole_0 @ X10)
% 0.38/0.57          | ~ (l1_struct_0 @ X11)
% 0.38/0.57          | (v2_struct_0 @ X11)
% 0.38/0.57          | (v1_xboole_0 @ X12)
% 0.38/0.57          | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.38/0.57          | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.38/0.57          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X10))))
% 0.38/0.57          | (l1_waybel_0 @ (k3_yellow19 @ X11 @ X10 @ X12) @ X11))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.38/0.57  thf('77', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('78', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('79', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('80', plain,
% 0.38/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.38/0.57          | (v1_xboole_0 @ X10)
% 0.38/0.57          | ~ (l1_struct_0 @ X11)
% 0.38/0.57          | (v2_struct_0 @ X11)
% 0.38/0.57          | (v1_xboole_0 @ X12)
% 0.38/0.57          | ~ (v2_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.38/0.57          | ~ (v13_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.38/0.57          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.57               (k1_zfmisc_1 @ 
% 0.38/0.57                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X10)))))
% 0.38/0.57          | (l1_waybel_0 @ (k3_yellow19 @ X11 @ X10 @ X12) @ X11))),
% 0.38/0.57      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 0.38/0.57  thf('81', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.57          | ~ (v13_waybel_0 @ sk_B @ 
% 0.38/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57          | ~ (v2_waybel_0 @ sk_B @ 
% 0.38/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | (v2_struct_0 @ X0)
% 0.38/0.57          | ~ (l1_struct_0 @ X0)
% 0.38/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['75', '80'])).
% 0.38/0.57  thf('82', plain,
% 0.38/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['30', '31'])).
% 0.38/0.57  thf('83', plain,
% 0.38/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.38/0.57  thf('84', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | (v2_struct_0 @ X0)
% 0.38/0.57          | ~ (l1_struct_0 @ X0)
% 0.38/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.57      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.38/0.57  thf('85', plain,
% 0.38/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57        | (v2_struct_0 @ sk_A)
% 0.38/0.57        | (v1_xboole_0 @ sk_B)
% 0.38/0.57        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.57           sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['74', '84'])).
% 0.38/0.57  thf('86', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.57           sk_A)
% 0.38/0.57        | (v1_xboole_0 @ sk_B)
% 0.38/0.57        | (v2_struct_0 @ sk_A)
% 0.38/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['73', '85'])).
% 0.38/0.57  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('88', plain,
% 0.38/0.57      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.57         sk_A)
% 0.38/0.57        | (v1_xboole_0 @ sk_B)
% 0.38/0.57        | (v2_struct_0 @ sk_A)
% 0.38/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['86', '87'])).
% 0.38/0.57  thf('89', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf('90', plain,
% 0.38/0.57      (![X6 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('91', plain,
% 0.38/0.57      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.57        | (r2_hidden @ sk_C @ 
% 0.38/0.57           (k10_yellow_6 @ sk_A @ 
% 0.38/0.57            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('92', plain,
% 0.38/0.57      (((r2_hidden @ sk_C @ 
% 0.38/0.57         (k10_yellow_6 @ sk_A @ 
% 0.38/0.57          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.38/0.57         <= (((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('split', [status(esa)], ['91'])).
% 0.38/0.57  thf('93', plain,
% 0.38/0.57      ((((r2_hidden @ sk_C @ 
% 0.38/0.57          (k10_yellow_6 @ sk_A @ 
% 0.38/0.57           (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57         | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.57         <= (((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('sup+', [status(thm)], ['90', '92'])).
% 0.38/0.57  thf('94', plain,
% 0.38/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.38/0.57         | (r2_hidden @ sk_C @ 
% 0.38/0.57            (k10_yellow_6 @ sk_A @ 
% 0.38/0.57             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))))
% 0.38/0.57         <= (((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['89', '93'])).
% 0.38/0.57  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('96', plain,
% 0.38/0.57      (((r2_hidden @ sk_C @ 
% 0.38/0.57         (k10_yellow_6 @ sk_A @ 
% 0.38/0.57          (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.38/0.57         <= (((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('demod', [status(thm)], ['94', '95'])).
% 0.38/0.57  thf(t13_yellow19, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.38/0.57             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.38/0.57           ( ![C:$i]:
% 0.38/0.57             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.57               ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) <=>
% 0.38/0.57                 ( r2_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.38/0.57  thf('97', plain,
% 0.38/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.57         ((v2_struct_0 @ X19)
% 0.38/0.57          | ~ (v4_orders_2 @ X19)
% 0.38/0.57          | ~ (v7_waybel_0 @ X19)
% 0.38/0.57          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.38/0.57          | ~ (r2_hidden @ X21 @ (k10_yellow_6 @ X20 @ X19))
% 0.38/0.57          | (r2_waybel_7 @ X20 @ (k2_yellow19 @ X20 @ X19) @ X21)
% 0.38/0.57          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.38/0.57          | ~ (l1_pre_topc @ X20)
% 0.38/0.57          | ~ (v2_pre_topc @ X20)
% 0.38/0.57          | (v2_struct_0 @ X20))),
% 0.38/0.57      inference('cnf', [status(esa)], [t13_yellow19])).
% 0.38/0.57  thf('98', plain,
% 0.38/0.57      ((((v2_struct_0 @ sk_A)
% 0.38/0.57         | ~ (v2_pre_topc @ sk_A)
% 0.38/0.57         | ~ (l1_pre_topc @ sk_A)
% 0.38/0.57         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (r2_waybel_7 @ sk_A @ 
% 0.38/0.57            (k2_yellow19 @ sk_A @ 
% 0.38/0.57             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.38/0.57            sk_C)
% 0.38/0.57         | ~ (l1_waybel_0 @ 
% 0.38/0.57              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.38/0.57         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.38/0.57         <= (((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['96', '97'])).
% 0.38/0.57  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('101', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('102', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf('103', plain,
% 0.38/0.57      (![X6 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('104', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf('105', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.38/0.57  thf(t15_yellow19, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.57             ( v1_subset_1 @
% 0.38/0.57               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.38/0.57             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.57             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.38/0.57             ( m1_subset_1 @
% 0.38/0.57               B @ 
% 0.38/0.57               ( k1_zfmisc_1 @
% 0.38/0.57                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.38/0.57           ( ( B ) =
% 0.38/0.57             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.38/0.57  thf('106', plain,
% 0.38/0.57      (![X22 : $i, X23 : $i]:
% 0.38/0.57         ((v1_xboole_0 @ X22)
% 0.38/0.57          | ~ (v1_subset_1 @ X22 @ 
% 0.38/0.57               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X23))))
% 0.38/0.57          | ~ (v2_waybel_0 @ X22 @ (k3_yellow_1 @ (k2_struct_0 @ X23)))
% 0.38/0.57          | ~ (v13_waybel_0 @ X22 @ (k3_yellow_1 @ (k2_struct_0 @ X23)))
% 0.38/0.57          | ~ (m1_subset_1 @ X22 @ 
% 0.38/0.57               (k1_zfmisc_1 @ 
% 0.38/0.57                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X23)))))
% 0.38/0.57          | ((X22)
% 0.38/0.57              = (k2_yellow19 @ X23 @ 
% 0.38/0.57                 (k3_yellow19 @ X23 @ (k2_struct_0 @ X23) @ X22)))
% 0.38/0.57          | ~ (l1_struct_0 @ X23)
% 0.38/0.57          | (v2_struct_0 @ X23))),
% 0.38/0.57      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.38/0.57  thf('107', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('108', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('109', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('110', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('111', plain,
% 0.38/0.57      (![X22 : $i, X23 : $i]:
% 0.38/0.57         ((v1_xboole_0 @ X22)
% 0.38/0.57          | ~ (v1_subset_1 @ X22 @ 
% 0.38/0.57               (u1_struct_0 @ 
% 0.38/0.57                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X23)))))
% 0.38/0.57          | ~ (v2_waybel_0 @ X22 @ 
% 0.38/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X23))))
% 0.38/0.57          | ~ (v13_waybel_0 @ X22 @ 
% 0.38/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X23))))
% 0.38/0.57          | ~ (m1_subset_1 @ X22 @ 
% 0.38/0.57               (k1_zfmisc_1 @ 
% 0.38/0.57                (u1_struct_0 @ 
% 0.38/0.57                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X23))))))
% 0.38/0.57          | ((X22)
% 0.38/0.57              = (k2_yellow19 @ X23 @ 
% 0.38/0.57                 (k3_yellow19 @ X23 @ (k2_struct_0 @ X23) @ X22)))
% 0.38/0.57          | ~ (l1_struct_0 @ X23)
% 0.38/0.57          | (v2_struct_0 @ X23))),
% 0.38/0.57      inference('demod', [status(thm)], ['106', '107', '108', '109', '110'])).
% 0.38/0.57  thf('112', plain,
% 0.38/0.57      (((v2_struct_0 @ sk_A)
% 0.38/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57        | ((sk_B)
% 0.38/0.57            = (k2_yellow19 @ sk_A @ 
% 0.38/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57        | ~ (v13_waybel_0 @ sk_B @ 
% 0.38/0.57             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.57        | ~ (v2_waybel_0 @ sk_B @ 
% 0.38/0.57             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.57        | ~ (v1_subset_1 @ sk_B @ 
% 0.38/0.57             (u1_struct_0 @ 
% 0.38/0.57              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.38/0.57        | (v1_xboole_0 @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['105', '111'])).
% 0.38/0.57  thf('113', plain,
% 0.38/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.57  thf('114', plain,
% 0.38/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.38/0.57  thf('115', plain,
% 0.38/0.57      ((v1_subset_1 @ sk_B @ 
% 0.38/0.57        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.38/0.57      inference('demod', [status(thm)], ['61', '62'])).
% 0.38/0.57  thf('116', plain,
% 0.38/0.57      (((v2_struct_0 @ sk_A)
% 0.38/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57        | ((sk_B)
% 0.38/0.57            = (k2_yellow19 @ sk_A @ 
% 0.38/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57        | (v1_xboole_0 @ sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 0.38/0.57  thf('117', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | (v1_xboole_0 @ sk_B)
% 0.38/0.57        | ((sk_B)
% 0.38/0.57            = (k2_yellow19 @ sk_A @ 
% 0.38/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57        | (v2_struct_0 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['104', '116'])).
% 0.38/0.57  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('119', plain,
% 0.38/0.57      (((v1_xboole_0 @ sk_B)
% 0.38/0.57        | ((sk_B)
% 0.38/0.57            = (k2_yellow19 @ sk_A @ 
% 0.38/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57        | (v2_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['117', '118'])).
% 0.38/0.57  thf('120', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('121', plain,
% 0.38/0.57      (((v2_struct_0 @ sk_A)
% 0.38/0.57        | ((sk_B)
% 0.38/0.57            = (k2_yellow19 @ sk_A @ 
% 0.38/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.38/0.57      inference('clc', [status(thm)], ['119', '120'])).
% 0.38/0.57  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('123', plain,
% 0.38/0.57      (((sk_B)
% 0.38/0.57         = (k2_yellow19 @ sk_A @ 
% 0.38/0.57            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('clc', [status(thm)], ['121', '122'])).
% 0.38/0.57  thf('124', plain,
% 0.38/0.57      ((((sk_B)
% 0.38/0.57          = (k2_yellow19 @ sk_A @ 
% 0.38/0.57             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.57      inference('sup+', [status(thm)], ['103', '123'])).
% 0.38/0.57  thf('125', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | ((sk_B)
% 0.38/0.57            = (k2_yellow19 @ sk_A @ 
% 0.38/0.57               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['102', '124'])).
% 0.38/0.57  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('127', plain,
% 0.38/0.57      (((sk_B)
% 0.38/0.57         = (k2_yellow19 @ sk_A @ 
% 0.38/0.57            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['125', '126'])).
% 0.38/0.57  thf('128', plain,
% 0.38/0.57      ((((v2_struct_0 @ sk_A)
% 0.38/0.57         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.57         | ~ (l1_waybel_0 @ 
% 0.38/0.57              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.38/0.57         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.38/0.57         <= (((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('demod', [status(thm)], ['98', '99', '100', '101', '127'])).
% 0.38/0.57  thf('129', plain,
% 0.38/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ sk_B)
% 0.38/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.57         | (v2_struct_0 @ sk_A)))
% 0.38/0.57         <= (((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['88', '128'])).
% 0.38/0.57  thf('130', plain,
% 0.38/0.57      ((((r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.57         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57         | (v1_xboole_0 @ sk_B)
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57         <= (((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('simplify', [status(thm)], ['129'])).
% 0.38/0.57  thf('131', plain,
% 0.38/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ sk_B)
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ sk_B)
% 0.38/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.38/0.57         <= (((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['72', '130'])).
% 0.38/0.57  thf('132', plain,
% 0.38/0.57      ((((r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.57         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57         | (v1_xboole_0 @ sk_B)
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57         <= (((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('simplify', [status(thm)], ['131'])).
% 0.38/0.57  thf('133', plain,
% 0.38/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ sk_B)
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ sk_B)
% 0.38/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.38/0.57         <= (((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['46', '132'])).
% 0.38/0.57  thf('134', plain,
% 0.38/0.57      ((((r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57         | (v1_xboole_0 @ sk_B)
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57         <= (((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('simplify', [status(thm)], ['133'])).
% 0.38/0.57  thf('135', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.57  thf('136', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.38/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.57  thf('137', plain,
% 0.38/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.38/0.57          | (v1_xboole_0 @ X10)
% 0.38/0.57          | ~ (l1_struct_0 @ X11)
% 0.38/0.57          | (v2_struct_0 @ X11)
% 0.38/0.57          | (v1_xboole_0 @ X12)
% 0.38/0.57          | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.38/0.57          | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.38/0.57          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X10))))
% 0.38/0.57          | ~ (v2_struct_0 @ (k3_yellow19 @ X11 @ X10 @ X12)))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.38/0.57  thf('138', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('139', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('140', plain,
% 0.38/0.57      (![X9 : $i]: ((k3_yellow_1 @ X9) = (k3_lattice3 @ (k1_lattice3 @ X9)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.38/0.57  thf('141', plain,
% 0.38/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.38/0.57          | (v1_xboole_0 @ X10)
% 0.38/0.57          | ~ (l1_struct_0 @ X11)
% 0.38/0.57          | (v2_struct_0 @ X11)
% 0.38/0.57          | (v1_xboole_0 @ X12)
% 0.38/0.57          | ~ (v2_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.38/0.57          | ~ (v13_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.38/0.57          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.57               (k1_zfmisc_1 @ 
% 0.38/0.57                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X10)))))
% 0.38/0.57          | ~ (v2_struct_0 @ (k3_yellow19 @ X11 @ X10 @ X12)))),
% 0.38/0.57      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 0.38/0.57  thf('142', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | ~ (v13_waybel_0 @ sk_B @ 
% 0.38/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57          | ~ (v2_waybel_0 @ sk_B @ 
% 0.38/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | (v2_struct_0 @ X0)
% 0.38/0.57          | ~ (l1_struct_0 @ X0)
% 0.38/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['136', '141'])).
% 0.38/0.57  thf('143', plain,
% 0.38/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['30', '31'])).
% 0.38/0.57  thf('144', plain,
% 0.38/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.38/0.57  thf('145', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | (v2_struct_0 @ X0)
% 0.38/0.57          | ~ (l1_struct_0 @ X0)
% 0.38/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.57      inference('demod', [status(thm)], ['142', '143', '144'])).
% 0.38/0.57  thf('146', plain,
% 0.38/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57        | (v2_struct_0 @ sk_A)
% 0.38/0.57        | (v1_xboole_0 @ sk_B)
% 0.38/0.57        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['135', '145'])).
% 0.38/0.57  thf('147', plain,
% 0.38/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ sk_B)
% 0.38/0.57         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.57         | (v1_xboole_0 @ sk_B)
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57         <= (((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['134', '146'])).
% 0.38/0.57  thf('148', plain,
% 0.38/0.57      (((~ (l1_struct_0 @ sk_A)
% 0.38/0.57         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.38/0.57         | (v1_xboole_0 @ sk_B)
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57         <= (((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('simplify', [status(thm)], ['147'])).
% 0.38/0.57  thf('149', plain,
% 0.38/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ sk_B)
% 0.38/0.57         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.38/0.57         <= (((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['3', '148'])).
% 0.38/0.57  thf('150', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('151', plain,
% 0.38/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ sk_B)
% 0.38/0.57         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.38/0.57         <= (((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('demod', [status(thm)], ['149', '150'])).
% 0.38/0.57  thf('152', plain,
% 0.38/0.57      ((~ (r2_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.38/0.57         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.57      inference('split', [status(esa)], ['0'])).
% 0.38/0.57  thf('153', plain,
% 0.38/0.57      ((((v1_xboole_0 @ sk_B)
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.57             ((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['151', '152'])).
% 0.38/0.57  thf('154', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('155', plain,
% 0.38/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.38/0.57         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.57             ((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('clc', [status(thm)], ['153', '154'])).
% 0.38/0.57  thf('156', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('157', plain,
% 0.38/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.38/0.57         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.57             ((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('clc', [status(thm)], ['155', '156'])).
% 0.38/0.57  thf('158', plain,
% 0.38/0.57      (![X6 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf(fc5_struct_0, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.57       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.38/0.57  thf('159', plain,
% 0.38/0.57      (![X8 : $i]:
% 0.38/0.57         (~ (v1_xboole_0 @ (k2_struct_0 @ X8))
% 0.38/0.57          | ~ (l1_struct_0 @ X8)
% 0.38/0.57          | (v2_struct_0 @ X8))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.38/0.57  thf('160', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.38/0.57          | ~ (l1_struct_0 @ X0)
% 0.38/0.57          | (v2_struct_0 @ X0)
% 0.38/0.57          | ~ (l1_struct_0 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['158', '159'])).
% 0.38/0.57  thf('161', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v2_struct_0 @ X0)
% 0.38/0.57          | ~ (l1_struct_0 @ X0)
% 0.38/0.57          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['160'])).
% 0.38/0.57  thf('162', plain,
% 0.38/0.57      (((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.38/0.57         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.57             ((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['157', '161'])).
% 0.38/0.57  thf('163', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('164', plain,
% 0.38/0.57      ((~ (l1_struct_0 @ sk_A))
% 0.38/0.57         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.57             ((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('clc', [status(thm)], ['162', '163'])).
% 0.38/0.57  thf('165', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A))
% 0.38/0.57         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.38/0.57             ((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['2', '164'])).
% 0.38/0.57  thf('166', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('167', plain,
% 0.38/0.57      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.38/0.57       ~
% 0.38/0.57       ((r2_hidden @ sk_C @ 
% 0.38/0.57         (k10_yellow_6 @ sk_A @ 
% 0.38/0.57          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.38/0.57      inference('demod', [status(thm)], ['165', '166'])).
% 0.38/0.57  thf('168', plain,
% 0.38/0.57      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.38/0.57       ((r2_hidden @ sk_C @ 
% 0.38/0.57         (k10_yellow_6 @ sk_A @ 
% 0.38/0.57          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.38/0.57      inference('split', [status(esa)], ['91'])).
% 0.38/0.57  thf('169', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf('170', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf('171', plain,
% 0.38/0.57      (![X6 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('172', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf('173', plain,
% 0.38/0.57      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.38/0.57         <= (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.57      inference('split', [status(esa)], ['91'])).
% 0.38/0.57  thf('174', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf('175', plain,
% 0.38/0.57      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57        | (v1_xboole_0 @ sk_B)
% 0.38/0.57        | (v2_struct_0 @ sk_A)
% 0.38/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['70', '71'])).
% 0.38/0.57  thf('176', plain,
% 0.38/0.57      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57        | (v1_xboole_0 @ sk_B)
% 0.38/0.57        | (v2_struct_0 @ sk_A)
% 0.38/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['44', '45'])).
% 0.38/0.57  thf('177', plain,
% 0.38/0.57      (![X6 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('178', plain,
% 0.38/0.57      (![X6 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('179', plain,
% 0.38/0.57      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.38/0.57         sk_A)
% 0.38/0.57        | (v1_xboole_0 @ sk_B)
% 0.38/0.57        | (v2_struct_0 @ sk_A)
% 0.38/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['86', '87'])).
% 0.38/0.57  thf('180', plain,
% 0.38/0.57      (![X6 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('181', plain,
% 0.38/0.57      (((sk_B)
% 0.38/0.57         = (k2_yellow19 @ sk_A @ 
% 0.38/0.57            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('clc', [status(thm)], ['121', '122'])).
% 0.38/0.57  thf('182', plain,
% 0.38/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.57         ((v2_struct_0 @ X19)
% 0.38/0.57          | ~ (v4_orders_2 @ X19)
% 0.38/0.57          | ~ (v7_waybel_0 @ X19)
% 0.38/0.57          | ~ (l1_waybel_0 @ X19 @ X20)
% 0.38/0.57          | ~ (r2_waybel_7 @ X20 @ (k2_yellow19 @ X20 @ X19) @ X21)
% 0.38/0.57          | (r2_hidden @ X21 @ (k10_yellow_6 @ X20 @ X19))
% 0.38/0.57          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.38/0.57          | ~ (l1_pre_topc @ X20)
% 0.38/0.57          | ~ (v2_pre_topc @ X20)
% 0.38/0.57          | (v2_struct_0 @ X20))),
% 0.38/0.57      inference('cnf', [status(esa)], [t13_yellow19])).
% 0.38/0.57  thf('183', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.57          | (v2_struct_0 @ sk_A)
% 0.38/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | (r2_hidden @ X0 @ 
% 0.38/0.57             (k10_yellow_6 @ sk_A @ 
% 0.38/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57          | ~ (l1_waybel_0 @ 
% 0.38/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.38/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['181', '182'])).
% 0.38/0.57  thf('184', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('185', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('186', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.57          | (v2_struct_0 @ sk_A)
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | (r2_hidden @ X0 @ 
% 0.38/0.57             (k10_yellow_6 @ sk_A @ 
% 0.38/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57          | ~ (l1_waybel_0 @ 
% 0.38/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.38/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['183', '184', '185'])).
% 0.38/0.57  thf('187', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (l1_waybel_0 @ 
% 0.38/0.57             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.38/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | (r2_hidden @ X0 @ 
% 0.38/0.57             (k10_yellow_6 @ sk_A @ 
% 0.38/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | (v2_struct_0 @ sk_A)
% 0.38/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['180', '186'])).
% 0.38/0.57  thf('188', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | (v2_struct_0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.57          | (v2_struct_0 @ sk_A)
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | (r2_hidden @ X0 @ 
% 0.38/0.57             (k10_yellow_6 @ sk_A @ 
% 0.38/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['179', '187'])).
% 0.38/0.57  thf('189', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (l1_struct_0 @ sk_A)
% 0.38/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | (r2_hidden @ X0 @ 
% 0.38/0.57             (k10_yellow_6 @ sk_A @ 
% 0.38/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | (v2_struct_0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['188'])).
% 0.38/0.57  thf('190', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | (v2_struct_0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | (r2_hidden @ X0 @ 
% 0.38/0.57             (k10_yellow_6 @ sk_A @ 
% 0.38/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['178', '189'])).
% 0.38/0.57  thf('191', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | (r2_hidden @ X0 @ 
% 0.38/0.57             (k10_yellow_6 @ sk_A @ 
% 0.38/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | (v2_struct_0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['190'])).
% 0.38/0.57  thf('192', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | (v2_struct_0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | (r2_hidden @ X0 @ 
% 0.38/0.57             (k10_yellow_6 @ sk_A @ 
% 0.38/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['177', '191'])).
% 0.38/0.57  thf('193', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | (r2_hidden @ X0 @ 
% 0.38/0.57             (k10_yellow_6 @ sk_A @ 
% 0.38/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | (v2_struct_0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['192'])).
% 0.38/0.57  thf('194', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | (v2_struct_0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | (v2_struct_0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | (r2_hidden @ X0 @ 
% 0.38/0.57             (k10_yellow_6 @ sk_A @ 
% 0.38/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['176', '193'])).
% 0.38/0.57  thf('195', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | (r2_hidden @ X0 @ 
% 0.38/0.57             (k10_yellow_6 @ sk_A @ 
% 0.38/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | (v2_struct_0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['194'])).
% 0.38/0.57  thf('196', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | (v2_struct_0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | (v2_struct_0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | (r2_hidden @ X0 @ 
% 0.38/0.57             (k10_yellow_6 @ sk_A @ 
% 0.38/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['175', '195'])).
% 0.38/0.57  thf('197', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | (r2_hidden @ X0 @ 
% 0.38/0.57             (k10_yellow_6 @ sk_A @ 
% 0.38/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | (v2_struct_0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['196'])).
% 0.38/0.57  thf('198', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (l1_pre_topc @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | (v2_struct_0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | (r2_hidden @ X0 @ 
% 0.38/0.57             (k10_yellow_6 @ sk_A @ 
% 0.38/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['174', '197'])).
% 0.38/0.57  thf('199', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('200', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | (v2_struct_0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57          | (r2_hidden @ X0 @ 
% 0.38/0.57             (k10_yellow_6 @ sk_A @ 
% 0.38/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['198', '199'])).
% 0.38/0.57  thf('201', plain,
% 0.38/0.57      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57         | (r2_hidden @ sk_C @ 
% 0.38/0.57            (k10_yellow_6 @ sk_A @ 
% 0.38/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v1_xboole_0 @ sk_B)
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57         <= (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['173', '200'])).
% 0.38/0.57  thf('202', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('203', plain,
% 0.38/0.57      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57         | (r2_hidden @ sk_C @ 
% 0.38/0.57            (k10_yellow_6 @ sk_A @ 
% 0.38/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.38/0.57         | (v1_xboole_0 @ sk_B)
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57         <= (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.57      inference('demod', [status(thm)], ['201', '202'])).
% 0.38/0.57  thf('204', plain,
% 0.38/0.57      ((~ (r2_hidden @ sk_C @ 
% 0.38/0.57           (k10_yellow_6 @ sk_A @ 
% 0.38/0.57            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.38/0.57      inference('split', [status(esa)], ['0'])).
% 0.38/0.57  thf('205', plain,
% 0.38/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ sk_B)
% 0.38/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['203', '204'])).
% 0.38/0.57  thf('206', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.57  thf('207', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf('208', plain,
% 0.38/0.57      (![X6 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('209', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.38/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.38/0.57  thf('210', plain,
% 0.38/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.38/0.57          | (v1_xboole_0 @ X10)
% 0.38/0.57          | ~ (l1_struct_0 @ X11)
% 0.38/0.57          | (v2_struct_0 @ X11)
% 0.38/0.57          | (v1_xboole_0 @ X12)
% 0.38/0.57          | ~ (v2_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.38/0.57          | ~ (v13_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.38/0.57          | ~ (m1_subset_1 @ X12 @ 
% 0.38/0.57               (k1_zfmisc_1 @ 
% 0.38/0.57                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X10)))))
% 0.38/0.57          | ~ (v2_struct_0 @ (k3_yellow19 @ X11 @ X10 @ X12)))),
% 0.38/0.57      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 0.38/0.57  thf('211', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | ~ (v13_waybel_0 @ sk_B @ 
% 0.38/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.57          | ~ (v2_waybel_0 @ sk_B @ 
% 0.38/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | (v2_struct_0 @ X0)
% 0.38/0.57          | ~ (l1_struct_0 @ X0)
% 0.38/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.57          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['209', '210'])).
% 0.38/0.57  thf('212', plain,
% 0.38/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.38/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.57  thf('213', plain,
% 0.38/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.38/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.38/0.57  thf('214', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | (v2_struct_0 @ X0)
% 0.38/0.57          | ~ (l1_struct_0 @ X0)
% 0.38/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.57          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.57      inference('demod', [status(thm)], ['211', '212', '213'])).
% 0.38/0.57  thf('215', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.57          | ~ (l1_struct_0 @ X0)
% 0.38/0.57          | (v2_struct_0 @ X0)
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['208', '214'])).
% 0.38/0.57  thf('216', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (l1_pre_topc @ sk_A)
% 0.38/0.57          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | (v2_struct_0 @ X0)
% 0.38/0.57          | ~ (l1_struct_0 @ X0)
% 0.38/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['207', '215'])).
% 0.38/0.57  thf('217', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('218', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.38/0.57          | (v1_xboole_0 @ sk_B)
% 0.38/0.57          | (v2_struct_0 @ X0)
% 0.38/0.57          | ~ (l1_struct_0 @ X0)
% 0.38/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.57      inference('demod', [status(thm)], ['216', '217'])).
% 0.38/0.57  thf('219', plain,
% 0.38/0.57      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57        | (v2_struct_0 @ sk_A)
% 0.38/0.57        | (v1_xboole_0 @ sk_B)
% 0.38/0.57        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['206', '218'])).
% 0.38/0.57  thf('220', plain,
% 0.38/0.57      ((((v1_xboole_0 @ sk_B)
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v1_xboole_0 @ sk_B)
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['205', '219'])).
% 0.38/0.57  thf('221', plain,
% 0.38/0.57      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.57         | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ sk_B)))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['220'])).
% 0.38/0.57  thf('222', plain,
% 0.38/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ sk_B)
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['172', '221'])).
% 0.38/0.57  thf('223', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('224', plain,
% 0.38/0.57      ((((v1_xboole_0 @ sk_B)
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.57      inference('demod', [status(thm)], ['222', '223'])).
% 0.38/0.57  thf('225', plain,
% 0.38/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ sk_B)))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['171', '224'])).
% 0.38/0.57  thf('226', plain,
% 0.38/0.57      ((((v1_xboole_0 @ sk_B)
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['225'])).
% 0.38/0.57  thf('227', plain,
% 0.38/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ sk_B)))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['170', '226'])).
% 0.38/0.57  thf('228', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('229', plain,
% 0.38/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_xboole_0 @ sk_B)))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.57      inference('demod', [status(thm)], ['227', '228'])).
% 0.38/0.57  thf('230', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('231', plain,
% 0.38/0.57      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.57      inference('clc', [status(thm)], ['229', '230'])).
% 0.38/0.57  thf('232', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('233', plain,
% 0.38/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.57      inference('clc', [status(thm)], ['231', '232'])).
% 0.38/0.57  thf('234', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v2_struct_0 @ X0)
% 0.38/0.57          | ~ (l1_struct_0 @ X0)
% 0.38/0.57          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['160'])).
% 0.38/0.57  thf('235', plain,
% 0.38/0.57      (((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_hidden @ sk_C @ 
% 0.38/0.57               (k10_yellow_6 @ sk_A @ 
% 0.38/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['233', '234'])).
% 0.38/0.57  thf('236', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('237', plain,
% 0.38/0.58      ((~ (l1_struct_0 @ sk_A))
% 0.38/0.58         <= (~
% 0.38/0.58             ((r2_hidden @ sk_C @ 
% 0.38/0.58               (k10_yellow_6 @ sk_A @ 
% 0.38/0.58                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.58             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.58      inference('clc', [status(thm)], ['235', '236'])).
% 0.38/0.58  thf('238', plain,
% 0.38/0.58      ((~ (l1_pre_topc @ sk_A))
% 0.38/0.58         <= (~
% 0.38/0.58             ((r2_hidden @ sk_C @ 
% 0.38/0.58               (k10_yellow_6 @ sk_A @ 
% 0.38/0.58                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.38/0.58             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['169', '237'])).
% 0.38/0.58  thf('239', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('240', plain,
% 0.38/0.58      (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.38/0.58       ((r2_hidden @ sk_C @ 
% 0.38/0.58         (k10_yellow_6 @ sk_A @ 
% 0.38/0.58          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.38/0.58      inference('demod', [status(thm)], ['238', '239'])).
% 0.38/0.58  thf('241', plain, ($false),
% 0.38/0.58      inference('sat_resolution*', [status(thm)], ['1', '167', '168', '240'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
