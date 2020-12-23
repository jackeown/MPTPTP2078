%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gtvDZ7ik2E

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:51 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  258 ( 909 expanded)
%              Number of leaves         :   40 ( 298 expanded)
%              Depth                    :   36
%              Number of atoms          : 3254 (15890 expanded)
%              Number of equality atoms :   46 ( 240 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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

thf('4',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('7',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('9',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
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

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_subset_1 @ X14 @ ( u1_struct_0 @ ( k3_yellow_1 @ X12 ) ) )
      | ~ ( v2_waybel_0 @ X14 @ ( k3_yellow_1 @ X12 ) )
      | ~ ( v13_waybel_0 @ X14 @ ( k3_yellow_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X12 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X13 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('18',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('19',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('20',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('21',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_subset_1 @ X14 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) ) )
      | ~ ( v2_waybel_0 @ X14 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) )
      | ~ ( v13_waybel_0 @ X14 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X13 @ X12 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf('23',plain,(
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
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('25',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('26',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
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
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
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
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('43',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('46',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['23','32','41','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','51'])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('57',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
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

thf('59',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v2_waybel_0 @ X11 @ ( k3_yellow_1 @ X9 ) )
      | ~ ( v13_waybel_0 @ X11 @ ( k3_yellow_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X9 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('60',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('61',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('62',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('63',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v2_waybel_0 @ X11 @ ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) )
      | ~ ( v13_waybel_0 @ X11 @ ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X9 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X10 @ X9 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('66',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','67'])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('73',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

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

thf('75',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v2_waybel_0 @ X8 @ ( k3_yellow_1 @ X6 ) )
      | ~ ( v13_waybel_0 @ X8 @ ( k3_yellow_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X6 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X7 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('76',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('77',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('78',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('79',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v2_waybel_0 @ X8 @ ( k3_lattice3 @ ( k1_lattice3 @ X6 ) ) )
      | ~ ( v13_waybel_0 @ X8 @ ( k3_lattice3 @ ( k1_lattice3 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X6 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X7 @ X6 @ X8 ) @ X7 ) ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('82',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['73','83'])).

thf('85',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('89',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('90',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['90'])).

thf('92',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['89','91'])).

thf('93',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['88','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
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

thf('97',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v7_waybel_0 @ X15 )
      | ~ ( l1_waybel_0 @ X15 @ X16 )
      | ~ ( r3_waybel_9 @ X16 @ X15 @ X17 )
      | ( r1_waybel_7 @ X16 @ ( k2_yellow19 @ X16 @ X15 ) @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('98',plain,(
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
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['95','101'])).

thf('103',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['87','102'])).

thf('104',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
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
    inference('sup-',[status(thm)],['71','104'])).

thf('106',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['55','106'])).

thf('108',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('109',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('110',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('111',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

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

thf('112',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_subset_1 @ X18 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X19 ) ) ) )
      | ~ ( v2_waybel_0 @ X18 @ ( k3_yellow_1 @ ( k2_struct_0 @ X19 ) ) )
      | ~ ( v13_waybel_0 @ X18 @ ( k3_yellow_1 @ ( k2_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X19 ) ) ) ) )
      | ( X18
        = ( k2_yellow19 @ X19 @ ( k3_yellow19 @ X19 @ ( k2_struct_0 @ X19 ) @ X18 ) ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('113',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('114',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('115',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('116',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('117',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_subset_1 @ X18 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X19 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X18 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X19 ) ) ) )
      | ~ ( v13_waybel_0 @ X18 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X19 ) ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X19 ) ) ) ) ) )
      | ( X18
        = ( k2_yellow19 @ X19 @ ( k3_yellow19 @ X19 @ ( k2_struct_0 @ X19 ) @ X18 ) ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['111','117'])).

thf('119',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('120',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('121',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['118','119','120','121'])).

thf('123',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['110','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['109','129'])).

thf('131',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['108','130'])).

thf('132',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['107','133'])).

thf('135',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('137',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('138',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v2_waybel_0 @ X8 @ ( k3_yellow_1 @ X6 ) )
      | ~ ( v13_waybel_0 @ X8 @ ( k3_yellow_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X6 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X7 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('139',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('140',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('141',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('142',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v2_waybel_0 @ X8 @ ( k3_lattice3 @ ( k1_lattice3 @ X6 ) ) )
      | ~ ( v13_waybel_0 @ X8 @ ( k3_lattice3 @ ( k1_lattice3 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X6 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X7 @ X6 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['138','139','140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['137','142'])).

thf('144',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('145',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['136','146'])).

thf('148',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['135','147'])).

thf('149',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['3','149'])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('154',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('160',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['158','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','165'])).

thf('167',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['90'])).

thf('170',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('171',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('172',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('173',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['90'])).

thf('174',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('175',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('176',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('177',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('178',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v7_waybel_0 @ X15 )
      | ~ ( l1_waybel_0 @ X15 @ X16 )
      | ~ ( r1_waybel_7 @ X16 @ ( k2_yellow19 @ X16 @ X15 ) @ X17 )
      | ( r3_waybel_9 @ X16 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['176','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['175','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['174','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['173','188'])).

thf('190',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('193',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('194',plain,
    ( ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['191','194'])).

thf('196',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['172','195'])).

thf('197',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['136','146'])).

thf('200',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['171','201'])).

thf('203',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['204','205'])).

thf('207',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('210',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['210','211'])).

thf('213',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['170','212'])).

thf('214',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','168','169','215'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gtvDZ7ik2E
% 0.13/0.36  % Computer   : n018.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 10:36:27 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.40/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.61  % Solved by: fo/fo7.sh
% 0.40/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.61  % done 185 iterations in 0.132s
% 0.40/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.61  % SZS output start Refutation
% 0.40/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.40/0.61  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.40/0.61  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.40/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.61  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.40/0.61  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.40/0.61  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.40/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.61  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.40/0.61  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.40/0.61  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.40/0.61  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.40/0.61  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.40/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.61  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.40/0.61  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.40/0.61  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.40/0.61  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.40/0.61  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 0.40/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.61  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.40/0.61  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.40/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.61  thf(t17_yellow19, conjecture,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.61             ( v1_subset_1 @
% 0.40/0.61               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.61             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.61             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.61             ( m1_subset_1 @
% 0.40/0.61               B @ 
% 0.40/0.61               ( k1_zfmisc_1 @
% 0.40/0.61                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.61           ( ![C:$i]:
% 0.40/0.61             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.61               ( ( r3_waybel_9 @
% 0.40/0.61                   A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.40/0.61                 ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.61    (~( ![A:$i]:
% 0.40/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.40/0.61            ( l1_pre_topc @ A ) ) =>
% 0.40/0.61          ( ![B:$i]:
% 0.40/0.61            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.61                ( v1_subset_1 @
% 0.40/0.61                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.61                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.61                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.61                ( m1_subset_1 @
% 0.40/0.61                  B @ 
% 0.40/0.61                  ( k1_zfmisc_1 @
% 0.40/0.61                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.61              ( ![C:$i]:
% 0.40/0.61                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.61                  ( ( r3_waybel_9 @
% 0.40/0.61                      A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.40/0.61                    ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.40/0.61    inference('cnf.neg', [status(esa)], [t17_yellow19])).
% 0.40/0.61  thf('0', plain,
% 0.40/0.61      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.61        | ~ (r3_waybel_9 @ sk_A @ 
% 0.40/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('1', plain,
% 0.40/0.61      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.40/0.61       ~
% 0.40/0.61       ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.61      inference('split', [status(esa)], ['0'])).
% 0.40/0.61  thf(dt_l1_pre_topc, axiom,
% 0.40/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.40/0.61  thf('2', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.61  thf('3', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.61  thf('4', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.61  thf(dt_k2_subset_1, axiom,
% 0.40/0.61    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.40/0.61  thf('5', plain,
% 0.40/0.61      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.40/0.61  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.40/0.61  thf('6', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.40/0.61      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.40/0.61  thf('7', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.40/0.61      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.61  thf('8', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.61  thf(d3_struct_0, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.40/0.61  thf('9', plain,
% 0.40/0.61      (![X2 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.61  thf('10', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_B @ 
% 0.40/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(d2_yellow_1, axiom,
% 0.40/0.61    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.40/0.61  thf('11', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('12', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_B @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.40/0.61  thf('13', plain,
% 0.40/0.61      (((m1_subset_1 @ sk_B @ 
% 0.40/0.61         (k1_zfmisc_1 @ 
% 0.40/0.61          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.61      inference('sup+', [status(thm)], ['9', '12'])).
% 0.40/0.61  thf('14', plain,
% 0.40/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.61        | (m1_subset_1 @ sk_B @ 
% 0.40/0.61           (k1_zfmisc_1 @ 
% 0.40/0.61            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['8', '13'])).
% 0.40/0.61  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('16', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_B @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.40/0.61      inference('demod', [status(thm)], ['14', '15'])).
% 0.40/0.61  thf(fc5_yellow19, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.40/0.61         ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.40/0.61         ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.61         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.40/0.61         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.61         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.61         ( m1_subset_1 @
% 0.40/0.61           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.40/0.61       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.40/0.61         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.40/0.61         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.40/0.61  thf('17', plain,
% 0.40/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.40/0.61          | (v1_xboole_0 @ X12)
% 0.40/0.61          | ~ (l1_struct_0 @ X13)
% 0.40/0.61          | (v2_struct_0 @ X13)
% 0.40/0.61          | (v1_xboole_0 @ X14)
% 0.40/0.61          | ~ (v1_subset_1 @ X14 @ (u1_struct_0 @ (k3_yellow_1 @ X12)))
% 0.40/0.61          | ~ (v2_waybel_0 @ X14 @ (k3_yellow_1 @ X12))
% 0.40/0.61          | ~ (v13_waybel_0 @ X14 @ (k3_yellow_1 @ X12))
% 0.40/0.61          | ~ (m1_subset_1 @ X14 @ 
% 0.40/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X12))))
% 0.40/0.61          | (v7_waybel_0 @ (k3_yellow19 @ X13 @ X12 @ X14)))),
% 0.40/0.61      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.40/0.61  thf('18', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('19', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('20', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('21', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('22', plain,
% 0.40/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.40/0.61          | (v1_xboole_0 @ X12)
% 0.40/0.61          | ~ (l1_struct_0 @ X13)
% 0.40/0.61          | (v2_struct_0 @ X13)
% 0.40/0.61          | (v1_xboole_0 @ X14)
% 0.40/0.61          | ~ (v1_subset_1 @ X14 @ 
% 0.40/0.61               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X12))))
% 0.40/0.61          | ~ (v2_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.40/0.61          | ~ (v13_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.40/0.61          | ~ (m1_subset_1 @ X14 @ 
% 0.40/0.61               (k1_zfmisc_1 @ 
% 0.40/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X12)))))
% 0.40/0.61          | (v7_waybel_0 @ (k3_yellow19 @ X13 @ X12 @ X14)))),
% 0.40/0.61      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 0.40/0.61  thf('23', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.61          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.61          | ~ (v1_subset_1 @ sk_B @ 
% 0.40/0.61               (u1_struct_0 @ 
% 0.40/0.61                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.40/0.61          | (v1_xboole_0 @ sk_B)
% 0.40/0.61          | (v2_struct_0 @ X0)
% 0.40/0.61          | ~ (l1_struct_0 @ X0)
% 0.40/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['16', '22'])).
% 0.40/0.61  thf('24', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.61  thf('25', plain,
% 0.40/0.61      (![X2 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.61  thf('26', plain,
% 0.40/0.61      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('27', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('28', plain,
% 0.40/0.61      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.40/0.61  thf('29', plain,
% 0.40/0.61      (((v13_waybel_0 @ sk_B @ 
% 0.40/0.61         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.61      inference('sup+', [status(thm)], ['25', '28'])).
% 0.40/0.61  thf('30', plain,
% 0.40/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.61        | (v13_waybel_0 @ sk_B @ 
% 0.40/0.61           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['24', '29'])).
% 0.40/0.61  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('32', plain,
% 0.40/0.61      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['30', '31'])).
% 0.40/0.61  thf('33', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.61  thf('34', plain,
% 0.40/0.61      (![X2 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.61  thf('35', plain,
% 0.40/0.61      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('36', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('37', plain,
% 0.40/0.61      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['35', '36'])).
% 0.40/0.61  thf('38', plain,
% 0.40/0.61      (((v2_waybel_0 @ sk_B @ 
% 0.40/0.61         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.61      inference('sup+', [status(thm)], ['34', '37'])).
% 0.40/0.61  thf('39', plain,
% 0.40/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.61        | (v2_waybel_0 @ sk_B @ 
% 0.40/0.61           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['33', '38'])).
% 0.40/0.61  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('41', plain,
% 0.40/0.61      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['39', '40'])).
% 0.40/0.61  thf('42', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.61  thf('43', plain,
% 0.40/0.61      (![X2 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.61  thf('44', plain,
% 0.40/0.61      ((v1_subset_1 @ sk_B @ 
% 0.40/0.61        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('45', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('46', plain,
% 0.40/0.61      ((v1_subset_1 @ sk_B @ 
% 0.40/0.61        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.61      inference('demod', [status(thm)], ['44', '45'])).
% 0.40/0.61  thf('47', plain,
% 0.40/0.61      (((v1_subset_1 @ sk_B @ 
% 0.40/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.61      inference('sup+', [status(thm)], ['43', '46'])).
% 0.40/0.61  thf('48', plain,
% 0.40/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.61        | (v1_subset_1 @ sk_B @ 
% 0.40/0.61           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['42', '47'])).
% 0.40/0.61  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('50', plain,
% 0.40/0.61      ((v1_subset_1 @ sk_B @ 
% 0.40/0.61        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.61      inference('demod', [status(thm)], ['48', '49'])).
% 0.40/0.61  thf('51', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | (v1_xboole_0 @ sk_B)
% 0.40/0.61          | (v2_struct_0 @ X0)
% 0.40/0.61          | ~ (l1_struct_0 @ X0)
% 0.40/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.61      inference('demod', [status(thm)], ['23', '32', '41', '50'])).
% 0.40/0.61  thf('52', plain,
% 0.40/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.61        | (v2_struct_0 @ sk_A)
% 0.40/0.61        | (v1_xboole_0 @ sk_B)
% 0.40/0.61        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['7', '51'])).
% 0.40/0.61  thf('53', plain,
% 0.40/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.61        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61        | (v1_xboole_0 @ sk_B)
% 0.40/0.61        | (v2_struct_0 @ sk_A)
% 0.40/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['4', '52'])).
% 0.40/0.61  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('55', plain,
% 0.40/0.61      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61        | (v1_xboole_0 @ sk_B)
% 0.40/0.61        | (v2_struct_0 @ sk_A)
% 0.40/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['53', '54'])).
% 0.40/0.61  thf('56', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.61  thf('57', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.40/0.61      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.61  thf('58', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_B @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.40/0.61      inference('demod', [status(thm)], ['14', '15'])).
% 0.40/0.61  thf(fc4_yellow19, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.40/0.61         ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.40/0.61         ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.61         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.61         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.61         ( m1_subset_1 @
% 0.40/0.61           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.40/0.61       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.40/0.61         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.40/0.61         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.40/0.61         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.40/0.61  thf('59', plain,
% 0.40/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.40/0.61          | (v1_xboole_0 @ X9)
% 0.40/0.61          | ~ (l1_struct_0 @ X10)
% 0.40/0.61          | (v2_struct_0 @ X10)
% 0.40/0.61          | (v1_xboole_0 @ X11)
% 0.40/0.61          | ~ (v2_waybel_0 @ X11 @ (k3_yellow_1 @ X9))
% 0.40/0.61          | ~ (v13_waybel_0 @ X11 @ (k3_yellow_1 @ X9))
% 0.40/0.61          | ~ (m1_subset_1 @ X11 @ 
% 0.40/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X9))))
% 0.40/0.61          | (v4_orders_2 @ (k3_yellow19 @ X10 @ X9 @ X11)))),
% 0.40/0.61      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.40/0.61  thf('60', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('61', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('62', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('63', plain,
% 0.40/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.40/0.61          | (v1_xboole_0 @ X9)
% 0.40/0.61          | ~ (l1_struct_0 @ X10)
% 0.40/0.61          | (v2_struct_0 @ X10)
% 0.40/0.61          | (v1_xboole_0 @ X11)
% 0.40/0.61          | ~ (v2_waybel_0 @ X11 @ (k3_lattice3 @ (k1_lattice3 @ X9)))
% 0.40/0.61          | ~ (v13_waybel_0 @ X11 @ (k3_lattice3 @ (k1_lattice3 @ X9)))
% 0.40/0.61          | ~ (m1_subset_1 @ X11 @ 
% 0.40/0.61               (k1_zfmisc_1 @ 
% 0.40/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X9)))))
% 0.40/0.61          | (v4_orders_2 @ (k3_yellow19 @ X10 @ X9 @ X11)))),
% 0.40/0.61      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.40/0.61  thf('64', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.61          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.61          | (v1_xboole_0 @ sk_B)
% 0.40/0.61          | (v2_struct_0 @ X0)
% 0.40/0.61          | ~ (l1_struct_0 @ X0)
% 0.40/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['58', '63'])).
% 0.40/0.61  thf('65', plain,
% 0.40/0.61      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['30', '31'])).
% 0.40/0.61  thf('66', plain,
% 0.40/0.61      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['39', '40'])).
% 0.40/0.61  thf('67', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | (v1_xboole_0 @ sk_B)
% 0.40/0.61          | (v2_struct_0 @ X0)
% 0.40/0.61          | ~ (l1_struct_0 @ X0)
% 0.40/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.61      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.40/0.61  thf('68', plain,
% 0.40/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.61        | (v2_struct_0 @ sk_A)
% 0.40/0.61        | (v1_xboole_0 @ sk_B)
% 0.40/0.61        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['57', '67'])).
% 0.40/0.61  thf('69', plain,
% 0.40/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.61        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61        | (v1_xboole_0 @ sk_B)
% 0.40/0.61        | (v2_struct_0 @ sk_A)
% 0.40/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['56', '68'])).
% 0.40/0.61  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('71', plain,
% 0.40/0.61      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61        | (v1_xboole_0 @ sk_B)
% 0.40/0.61        | (v2_struct_0 @ sk_A)
% 0.40/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['69', '70'])).
% 0.40/0.61  thf('72', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.61  thf('73', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.40/0.61      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.61  thf('74', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_B @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.40/0.61      inference('demod', [status(thm)], ['14', '15'])).
% 0.40/0.61  thf(dt_k3_yellow19, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.40/0.61         ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.40/0.61         ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.61         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.61         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.61         ( m1_subset_1 @
% 0.40/0.61           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.40/0.61       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.40/0.61         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.40/0.61         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.40/0.61  thf('75', plain,
% 0.40/0.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.40/0.61          | (v1_xboole_0 @ X6)
% 0.40/0.61          | ~ (l1_struct_0 @ X7)
% 0.40/0.61          | (v2_struct_0 @ X7)
% 0.40/0.61          | (v1_xboole_0 @ X8)
% 0.40/0.61          | ~ (v2_waybel_0 @ X8 @ (k3_yellow_1 @ X6))
% 0.40/0.61          | ~ (v13_waybel_0 @ X8 @ (k3_yellow_1 @ X6))
% 0.40/0.61          | ~ (m1_subset_1 @ X8 @ 
% 0.40/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X6))))
% 0.40/0.61          | (l1_waybel_0 @ (k3_yellow19 @ X7 @ X6 @ X8) @ X7))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.40/0.61  thf('76', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('77', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('78', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('79', plain,
% 0.40/0.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.40/0.61          | (v1_xboole_0 @ X6)
% 0.40/0.61          | ~ (l1_struct_0 @ X7)
% 0.40/0.61          | (v2_struct_0 @ X7)
% 0.40/0.61          | (v1_xboole_0 @ X8)
% 0.40/0.61          | ~ (v2_waybel_0 @ X8 @ (k3_lattice3 @ (k1_lattice3 @ X6)))
% 0.40/0.61          | ~ (v13_waybel_0 @ X8 @ (k3_lattice3 @ (k1_lattice3 @ X6)))
% 0.40/0.61          | ~ (m1_subset_1 @ X8 @ 
% 0.40/0.61               (k1_zfmisc_1 @ 
% 0.40/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X6)))))
% 0.40/0.61          | (l1_waybel_0 @ (k3_yellow19 @ X7 @ X6 @ X8) @ X7))),
% 0.40/0.61      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.40/0.61  thf('80', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.61          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.61          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.61          | (v1_xboole_0 @ sk_B)
% 0.40/0.61          | (v2_struct_0 @ X0)
% 0.40/0.61          | ~ (l1_struct_0 @ X0)
% 0.40/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['74', '79'])).
% 0.40/0.61  thf('81', plain,
% 0.40/0.61      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['30', '31'])).
% 0.40/0.61  thf('82', plain,
% 0.40/0.61      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['39', '40'])).
% 0.40/0.61  thf('83', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.61          | (v1_xboole_0 @ sk_B)
% 0.40/0.61          | (v2_struct_0 @ X0)
% 0.40/0.61          | ~ (l1_struct_0 @ X0)
% 0.40/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.61      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.40/0.61  thf('84', plain,
% 0.40/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.61        | (v2_struct_0 @ sk_A)
% 0.40/0.61        | (v1_xboole_0 @ sk_B)
% 0.40/0.61        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.61           sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['73', '83'])).
% 0.40/0.61  thf('85', plain,
% 0.40/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.61        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.61           sk_A)
% 0.40/0.61        | (v1_xboole_0 @ sk_B)
% 0.40/0.61        | (v2_struct_0 @ sk_A)
% 0.40/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['72', '84'])).
% 0.40/0.61  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('87', plain,
% 0.40/0.61      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.61         sk_A)
% 0.40/0.61        | (v1_xboole_0 @ sk_B)
% 0.40/0.61        | (v2_struct_0 @ sk_A)
% 0.40/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['85', '86'])).
% 0.40/0.61  thf('88', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.61  thf('89', plain,
% 0.40/0.61      (![X2 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.61  thf('90', plain,
% 0.40/0.61      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.61        | (r3_waybel_9 @ sk_A @ 
% 0.40/0.61           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('91', plain,
% 0.40/0.61      (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('split', [status(esa)], ['90'])).
% 0.40/0.61  thf('92', plain,
% 0.40/0.61      ((((r3_waybel_9 @ sk_A @ 
% 0.40/0.61          (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.40/0.61         | ~ (l1_struct_0 @ sk_A)))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['89', '91'])).
% 0.40/0.61  thf('93', plain,
% 0.40/0.61      (((~ (l1_pre_topc @ sk_A)
% 0.40/0.61         | (r3_waybel_9 @ sk_A @ 
% 0.40/0.61            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C)))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['88', '92'])).
% 0.40/0.61  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('95', plain,
% 0.40/0.61      (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61         (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('demod', [status(thm)], ['93', '94'])).
% 0.40/0.61  thf('96', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(t12_yellow19, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.40/0.61             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.40/0.61           ( ![C:$i]:
% 0.40/0.61             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.61               ( ( r3_waybel_9 @ A @ B @ C ) <=>
% 0.40/0.61                 ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.40/0.61  thf('97', plain,
% 0.40/0.61      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.61         ((v2_struct_0 @ X15)
% 0.40/0.61          | ~ (v4_orders_2 @ X15)
% 0.40/0.61          | ~ (v7_waybel_0 @ X15)
% 0.40/0.61          | ~ (l1_waybel_0 @ X15 @ X16)
% 0.40/0.61          | ~ (r3_waybel_9 @ X16 @ X15 @ X17)
% 0.40/0.61          | (r1_waybel_7 @ X16 @ (k2_yellow19 @ X16 @ X15) @ X17)
% 0.40/0.61          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.40/0.61          | ~ (l1_pre_topc @ X16)
% 0.40/0.61          | ~ (v2_pre_topc @ X16)
% 0.40/0.61          | (v2_struct_0 @ X16))),
% 0.40/0.61      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.40/0.61  thf('98', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((v2_struct_0 @ sk_A)
% 0.40/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.40/0.61          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.40/0.61          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.40/0.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.40/0.61          | ~ (v7_waybel_0 @ X0)
% 0.40/0.61          | ~ (v4_orders_2 @ X0)
% 0.40/0.61          | (v2_struct_0 @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['96', '97'])).
% 0.40/0.61  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('101', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((v2_struct_0 @ sk_A)
% 0.40/0.61          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.40/0.61          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.40/0.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.40/0.61          | ~ (v7_waybel_0 @ X0)
% 0.40/0.61          | ~ (v4_orders_2 @ X0)
% 0.40/0.61          | (v2_struct_0 @ X0))),
% 0.40/0.61      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.40/0.61  thf('102', plain,
% 0.40/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61         | ~ (l1_waybel_0 @ 
% 0.40/0.61              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.40/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.61            (k2_yellow19 @ sk_A @ 
% 0.40/0.61             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.61            sk_C)
% 0.40/0.61         | (v2_struct_0 @ sk_A)))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['95', '101'])).
% 0.40/0.61  thf('103', plain,
% 0.40/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.61            (k2_yellow19 @ sk_A @ 
% 0.40/0.61             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.61            sk_C)
% 0.40/0.61         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['87', '102'])).
% 0.40/0.61  thf('104', plain,
% 0.40/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.61            (k2_yellow19 @ sk_A @ 
% 0.40/0.61             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.61            sk_C)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['103'])).
% 0.40/0.61  thf('105', plain,
% 0.40/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)
% 0.40/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.61            (k2_yellow19 @ sk_A @ 
% 0.40/0.61             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.61            sk_C)
% 0.40/0.61         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['71', '104'])).
% 0.40/0.61  thf('106', plain,
% 0.40/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.61            (k2_yellow19 @ sk_A @ 
% 0.40/0.61             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.61            sk_C)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['105'])).
% 0.40/0.61  thf('107', plain,
% 0.40/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)
% 0.40/0.61         | (r1_waybel_7 @ sk_A @ 
% 0.40/0.61            (k2_yellow19 @ sk_A @ 
% 0.40/0.61             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.61            sk_C)
% 0.40/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['55', '106'])).
% 0.40/0.61  thf('108', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.61  thf('109', plain,
% 0.40/0.61      (![X2 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.61  thf('110', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.61  thf('111', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_B @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.40/0.61  thf(t15_yellow19, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.61             ( v1_subset_1 @
% 0.40/0.61               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.61             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.61             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.61             ( m1_subset_1 @
% 0.40/0.61               B @ 
% 0.40/0.61               ( k1_zfmisc_1 @
% 0.40/0.61                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.61           ( ( B ) =
% 0.40/0.61             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.40/0.61  thf('112', plain,
% 0.40/0.61      (![X18 : $i, X19 : $i]:
% 0.40/0.61         ((v1_xboole_0 @ X18)
% 0.40/0.61          | ~ (v1_subset_1 @ X18 @ 
% 0.40/0.61               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X19))))
% 0.40/0.61          | ~ (v2_waybel_0 @ X18 @ (k3_yellow_1 @ (k2_struct_0 @ X19)))
% 0.40/0.61          | ~ (v13_waybel_0 @ X18 @ (k3_yellow_1 @ (k2_struct_0 @ X19)))
% 0.40/0.61          | ~ (m1_subset_1 @ X18 @ 
% 0.40/0.61               (k1_zfmisc_1 @ 
% 0.40/0.61                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X19)))))
% 0.40/0.61          | ((X18)
% 0.40/0.61              = (k2_yellow19 @ X19 @ 
% 0.40/0.61                 (k3_yellow19 @ X19 @ (k2_struct_0 @ X19) @ X18)))
% 0.40/0.61          | ~ (l1_struct_0 @ X19)
% 0.40/0.61          | (v2_struct_0 @ X19))),
% 0.40/0.61      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.40/0.61  thf('113', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('114', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('115', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('116', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('117', plain,
% 0.40/0.61      (![X18 : $i, X19 : $i]:
% 0.40/0.61         ((v1_xboole_0 @ X18)
% 0.40/0.61          | ~ (v1_subset_1 @ X18 @ 
% 0.40/0.61               (u1_struct_0 @ 
% 0.40/0.61                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X19)))))
% 0.40/0.61          | ~ (v2_waybel_0 @ X18 @ 
% 0.40/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X19))))
% 0.40/0.61          | ~ (v13_waybel_0 @ X18 @ 
% 0.40/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X19))))
% 0.40/0.61          | ~ (m1_subset_1 @ X18 @ 
% 0.40/0.61               (k1_zfmisc_1 @ 
% 0.40/0.61                (u1_struct_0 @ 
% 0.40/0.61                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X19))))))
% 0.40/0.61          | ((X18)
% 0.40/0.61              = (k2_yellow19 @ X19 @ 
% 0.40/0.61                 (k3_yellow19 @ X19 @ (k2_struct_0 @ X19) @ X18)))
% 0.40/0.61          | ~ (l1_struct_0 @ X19)
% 0.40/0.61          | (v2_struct_0 @ X19))),
% 0.40/0.61      inference('demod', [status(thm)], ['112', '113', '114', '115', '116'])).
% 0.40/0.61  thf('118', plain,
% 0.40/0.61      (((v2_struct_0 @ sk_A)
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.61        | ((sk_B)
% 0.40/0.61            = (k2_yellow19 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.61        | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.61             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.61        | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.61             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.61        | ~ (v1_subset_1 @ sk_B @ 
% 0.40/0.61             (u1_struct_0 @ 
% 0.40/0.61              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.40/0.61        | (v1_xboole_0 @ sk_B))),
% 0.40/0.61      inference('sup-', [status(thm)], ['111', '117'])).
% 0.40/0.61  thf('119', plain,
% 0.40/0.61      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.40/0.61  thf('120', plain,
% 0.40/0.61      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['35', '36'])).
% 0.40/0.61  thf('121', plain,
% 0.40/0.61      ((v1_subset_1 @ sk_B @ 
% 0.40/0.61        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.61      inference('demod', [status(thm)], ['44', '45'])).
% 0.40/0.61  thf('122', plain,
% 0.40/0.61      (((v2_struct_0 @ sk_A)
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.61        | ((sk_B)
% 0.40/0.61            = (k2_yellow19 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.61        | (v1_xboole_0 @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['118', '119', '120', '121'])).
% 0.40/0.61  thf('123', plain,
% 0.40/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.61        | (v1_xboole_0 @ sk_B)
% 0.40/0.61        | ((sk_B)
% 0.40/0.61            = (k2_yellow19 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.61        | (v2_struct_0 @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['110', '122'])).
% 0.40/0.61  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('125', plain,
% 0.40/0.61      (((v1_xboole_0 @ sk_B)
% 0.40/0.61        | ((sk_B)
% 0.40/0.61            = (k2_yellow19 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.61        | (v2_struct_0 @ sk_A))),
% 0.40/0.61      inference('demod', [status(thm)], ['123', '124'])).
% 0.40/0.61  thf('126', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('127', plain,
% 0.40/0.61      (((v2_struct_0 @ sk_A)
% 0.40/0.61        | ((sk_B)
% 0.40/0.61            = (k2_yellow19 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.40/0.61      inference('clc', [status(thm)], ['125', '126'])).
% 0.40/0.61  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('129', plain,
% 0.40/0.61      (((sk_B)
% 0.40/0.61         = (k2_yellow19 @ sk_A @ 
% 0.40/0.61            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.61      inference('clc', [status(thm)], ['127', '128'])).
% 0.40/0.61  thf('130', plain,
% 0.40/0.61      ((((sk_B)
% 0.40/0.61          = (k2_yellow19 @ sk_A @ 
% 0.40/0.61             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.61      inference('sup+', [status(thm)], ['109', '129'])).
% 0.40/0.61  thf('131', plain,
% 0.40/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.61        | ((sk_B)
% 0.40/0.61            = (k2_yellow19 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['108', '130'])).
% 0.40/0.61  thf('132', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('133', plain,
% 0.40/0.61      (((sk_B)
% 0.40/0.61         = (k2_yellow19 @ sk_A @ 
% 0.40/0.61            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.61      inference('demod', [status(thm)], ['131', '132'])).
% 0.40/0.61  thf('134', plain,
% 0.40/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)
% 0.40/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.61         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('demod', [status(thm)], ['107', '133'])).
% 0.40/0.61  thf('135', plain,
% 0.40/0.61      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['134'])).
% 0.40/0.61  thf('136', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.40/0.61      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.61  thf('137', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_B @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.40/0.61      inference('demod', [status(thm)], ['14', '15'])).
% 0.40/0.61  thf('138', plain,
% 0.40/0.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.40/0.61          | (v1_xboole_0 @ X6)
% 0.40/0.61          | ~ (l1_struct_0 @ X7)
% 0.40/0.61          | (v2_struct_0 @ X7)
% 0.40/0.61          | (v1_xboole_0 @ X8)
% 0.40/0.61          | ~ (v2_waybel_0 @ X8 @ (k3_yellow_1 @ X6))
% 0.40/0.61          | ~ (v13_waybel_0 @ X8 @ (k3_yellow_1 @ X6))
% 0.40/0.61          | ~ (m1_subset_1 @ X8 @ 
% 0.40/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X6))))
% 0.40/0.61          | ~ (v2_struct_0 @ (k3_yellow19 @ X7 @ X6 @ X8)))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.40/0.61  thf('139', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('140', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('141', plain,
% 0.40/0.61      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.61  thf('142', plain,
% 0.40/0.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.40/0.61          | (v1_xboole_0 @ X6)
% 0.40/0.61          | ~ (l1_struct_0 @ X7)
% 0.40/0.61          | (v2_struct_0 @ X7)
% 0.40/0.61          | (v1_xboole_0 @ X8)
% 0.40/0.61          | ~ (v2_waybel_0 @ X8 @ (k3_lattice3 @ (k1_lattice3 @ X6)))
% 0.40/0.61          | ~ (v13_waybel_0 @ X8 @ (k3_lattice3 @ (k1_lattice3 @ X6)))
% 0.40/0.61          | ~ (m1_subset_1 @ X8 @ 
% 0.40/0.61               (k1_zfmisc_1 @ 
% 0.40/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X6)))))
% 0.40/0.61          | ~ (v2_struct_0 @ (k3_yellow19 @ X7 @ X6 @ X8)))),
% 0.40/0.61      inference('demod', [status(thm)], ['138', '139', '140', '141'])).
% 0.40/0.61  thf('143', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.61          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.61               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.61          | (v1_xboole_0 @ sk_B)
% 0.40/0.61          | (v2_struct_0 @ X0)
% 0.40/0.61          | ~ (l1_struct_0 @ X0)
% 0.40/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['137', '142'])).
% 0.40/0.61  thf('144', plain,
% 0.40/0.61      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['30', '31'])).
% 0.40/0.61  thf('145', plain,
% 0.40/0.61      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.61        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.61      inference('demod', [status(thm)], ['39', '40'])).
% 0.40/0.61  thf('146', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.61          | (v1_xboole_0 @ sk_B)
% 0.40/0.61          | (v2_struct_0 @ X0)
% 0.40/0.61          | ~ (l1_struct_0 @ X0)
% 0.40/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.61      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.40/0.61  thf('147', plain,
% 0.40/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.61        | (v2_struct_0 @ sk_A)
% 0.40/0.61        | (v1_xboole_0 @ sk_B)
% 0.40/0.61        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['136', '146'])).
% 0.40/0.61  thf('148', plain,
% 0.40/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)
% 0.40/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['135', '147'])).
% 0.40/0.61  thf('149', plain,
% 0.40/0.61      (((~ (l1_struct_0 @ sk_A)
% 0.40/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['148'])).
% 0.40/0.61  thf('150', plain,
% 0.40/0.61      (((~ (l1_pre_topc @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)
% 0.40/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['3', '149'])).
% 0.40/0.61  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('152', plain,
% 0.40/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ sk_B)
% 0.40/0.61         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.40/0.61         <= (((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('demod', [status(thm)], ['150', '151'])).
% 0.40/0.61  thf('153', plain,
% 0.40/0.61      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.40/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.61      inference('split', [status(esa)], ['0'])).
% 0.40/0.61  thf('154', plain,
% 0.40/0.61      ((((v1_xboole_0 @ sk_B)
% 0.40/0.61         | (v2_struct_0 @ sk_A)
% 0.40/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['152', '153'])).
% 0.40/0.61  thf('155', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('156', plain,
% 0.40/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.40/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('clc', [status(thm)], ['154', '155'])).
% 0.40/0.61  thf('157', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('158', plain,
% 0.40/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.40/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('clc', [status(thm)], ['156', '157'])).
% 0.40/0.61  thf('159', plain,
% 0.40/0.61      (![X2 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.61  thf(fc5_struct_0, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.40/0.61       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.40/0.61  thf('160', plain,
% 0.40/0.61      (![X4 : $i]:
% 0.40/0.61         (~ (v1_xboole_0 @ (k2_struct_0 @ X4))
% 0.40/0.61          | ~ (l1_struct_0 @ X4)
% 0.40/0.61          | (v2_struct_0 @ X4))),
% 0.40/0.61      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.40/0.61  thf('161', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.40/0.61          | ~ (l1_struct_0 @ X0)
% 0.40/0.61          | (v2_struct_0 @ X0)
% 0.40/0.61          | ~ (l1_struct_0 @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['159', '160'])).
% 0.40/0.61  thf('162', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((v2_struct_0 @ X0)
% 0.40/0.61          | ~ (l1_struct_0 @ X0)
% 0.40/0.61          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['161'])).
% 0.40/0.61  thf('163', plain,
% 0.40/0.61      (((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.40/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['158', '162'])).
% 0.40/0.61  thf('164', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('165', plain,
% 0.40/0.61      ((~ (l1_struct_0 @ sk_A))
% 0.40/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('clc', [status(thm)], ['163', '164'])).
% 0.40/0.61  thf('166', plain,
% 0.40/0.61      ((~ (l1_pre_topc @ sk_A))
% 0.40/0.61         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.61             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['2', '165'])).
% 0.40/0.61  thf('167', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('168', plain,
% 0.40/0.61      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.40/0.61       ~
% 0.40/0.61       ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.61      inference('demod', [status(thm)], ['166', '167'])).
% 0.40/0.61  thf('169', plain,
% 0.40/0.61      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.40/0.61       ((r3_waybel_9 @ sk_A @ 
% 0.40/0.61         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.61      inference('split', [status(esa)], ['90'])).
% 0.40/0.61  thf('170', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('171', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('172', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('173', plain,
% 0.40/0.62      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.40/0.62         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.62      inference('split', [status(esa)], ['90'])).
% 0.40/0.62  thf('174', plain,
% 0.40/0.62      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62        | (v1_xboole_0 @ sk_B)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.62      inference('demod', [status(thm)], ['69', '70'])).
% 0.40/0.62  thf('175', plain,
% 0.40/0.62      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62        | (v1_xboole_0 @ sk_B)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.62      inference('demod', [status(thm)], ['53', '54'])).
% 0.40/0.62  thf('176', plain,
% 0.40/0.62      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.62         sk_A)
% 0.40/0.62        | (v1_xboole_0 @ sk_B)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.62      inference('demod', [status(thm)], ['85', '86'])).
% 0.40/0.62  thf('177', plain,
% 0.40/0.62      (((sk_B)
% 0.40/0.62         = (k2_yellow19 @ sk_A @ 
% 0.40/0.62            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.62      inference('demod', [status(thm)], ['131', '132'])).
% 0.40/0.62  thf('178', plain,
% 0.40/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.62         ((v2_struct_0 @ X15)
% 0.40/0.62          | ~ (v4_orders_2 @ X15)
% 0.40/0.62          | ~ (v7_waybel_0 @ X15)
% 0.40/0.62          | ~ (l1_waybel_0 @ X15 @ X16)
% 0.40/0.62          | ~ (r1_waybel_7 @ X16 @ (k2_yellow19 @ X16 @ X15) @ X17)
% 0.40/0.62          | (r3_waybel_9 @ X16 @ X15 @ X17)
% 0.40/0.62          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.40/0.62          | ~ (l1_pre_topc @ X16)
% 0.40/0.62          | ~ (v2_pre_topc @ X16)
% 0.40/0.62          | (v2_struct_0 @ X16))),
% 0.40/0.62      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.40/0.62  thf('179', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.40/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.62             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.62          | ~ (l1_waybel_0 @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.40/0.62          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['177', '178'])).
% 0.40/0.62  thf('180', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('181', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('182', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.62             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.62          | ~ (l1_waybel_0 @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.40/0.62          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.62      inference('demod', [status(thm)], ['179', '180', '181'])).
% 0.40/0.62  thf('183', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | (v1_xboole_0 @ sk_B)
% 0.40/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.62             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['176', '182'])).
% 0.40/0.62  thf('184', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.62             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.62          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62          | (v1_xboole_0 @ sk_B)
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['183'])).
% 0.40/0.62  thf('185', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | (v1_xboole_0 @ sk_B)
% 0.40/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | (v1_xboole_0 @ sk_B)
% 0.40/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.62             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['175', '184'])).
% 0.40/0.62  thf('186', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.62             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.62          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62          | (v1_xboole_0 @ sk_B)
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['185'])).
% 0.40/0.62  thf('187', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | (v1_xboole_0 @ sk_B)
% 0.40/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | (v1_xboole_0 @ sk_B)
% 0.40/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.62             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['174', '186'])).
% 0.40/0.62  thf('188', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62          | (r3_waybel_9 @ sk_A @ 
% 0.40/0.62             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.62          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62          | (v1_xboole_0 @ sk_B)
% 0.40/0.62          | (v2_struct_0 @ sk_A)
% 0.40/0.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['187'])).
% 0.40/0.62  thf('189', plain,
% 0.40/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B)
% 0.40/0.62         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62         | (r3_waybel_9 @ sk_A @ 
% 0.40/0.62            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.40/0.62         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))))
% 0.40/0.62         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['173', '188'])).
% 0.40/0.62  thf('190', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('191', plain,
% 0.40/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B)
% 0.40/0.62         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62         | (r3_waybel_9 @ sk_A @ 
% 0.40/0.62            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C)))
% 0.40/0.62         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.62      inference('demod', [status(thm)], ['189', '190'])).
% 0.40/0.62  thf('192', plain,
% 0.40/0.62      (![X2 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('193', plain,
% 0.40/0.62      ((~ (r3_waybel_9 @ sk_A @ 
% 0.40/0.62           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.62      inference('split', [status(esa)], ['0'])).
% 0.40/0.62  thf('194', plain,
% 0.40/0.62      (((~ (r3_waybel_9 @ sk_A @ 
% 0.40/0.62            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.40/0.62         | ~ (l1_struct_0 @ sk_A)))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['192', '193'])).
% 0.40/0.62  thf('195', plain,
% 0.40/0.62      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.62         | (v1_xboole_0 @ sk_B)
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | ~ (l1_struct_0 @ sk_A)))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['191', '194'])).
% 0.40/0.62  thf('196', plain,
% 0.40/0.62      (((~ (l1_pre_topc @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B)
% 0.40/0.62         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['172', '195'])).
% 0.40/0.62  thf('197', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('198', plain,
% 0.40/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B)
% 0.40/0.62         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.62      inference('demod', [status(thm)], ['196', '197'])).
% 0.40/0.62  thf('199', plain,
% 0.40/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62        | (v2_struct_0 @ sk_A)
% 0.40/0.62        | (v1_xboole_0 @ sk_B)
% 0.40/0.62        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['136', '146'])).
% 0.40/0.62  thf('200', plain,
% 0.40/0.62      ((((v1_xboole_0 @ sk_B)
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v1_xboole_0 @ sk_B)
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['198', '199'])).
% 0.40/0.62  thf('201', plain,
% 0.40/0.62      (((~ (l1_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B)))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['200'])).
% 0.40/0.62  thf('202', plain,
% 0.40/0.62      (((~ (l1_pre_topc @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ sk_B)
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['171', '201'])).
% 0.40/0.62  thf('203', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('204', plain,
% 0.40/0.62      ((((v1_xboole_0 @ sk_B)
% 0.40/0.62         | (v2_struct_0 @ sk_A)
% 0.40/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.62      inference('demod', [status(thm)], ['202', '203'])).
% 0.40/0.62  thf('205', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('206', plain,
% 0.40/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.62      inference('clc', [status(thm)], ['204', '205'])).
% 0.40/0.62  thf('207', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('208', plain,
% 0.40/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.62      inference('clc', [status(thm)], ['206', '207'])).
% 0.40/0.62  thf('209', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v2_struct_0 @ X0)
% 0.40/0.62          | ~ (l1_struct_0 @ X0)
% 0.40/0.62          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['161'])).
% 0.40/0.62  thf('210', plain,
% 0.40/0.62      (((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['208', '209'])).
% 0.40/0.62  thf('211', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('212', plain,
% 0.40/0.62      ((~ (l1_struct_0 @ sk_A))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.62      inference('clc', [status(thm)], ['210', '211'])).
% 0.40/0.62  thf('213', plain,
% 0.40/0.62      ((~ (l1_pre_topc @ sk_A))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r3_waybel_9 @ sk_A @ 
% 0.40/0.62               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.40/0.62             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['170', '212'])).
% 0.40/0.62  thf('214', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('215', plain,
% 0.40/0.62      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.40/0.62       ((r3_waybel_9 @ sk_A @ 
% 0.40/0.62         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.40/0.62      inference('demod', [status(thm)], ['213', '214'])).
% 0.40/0.62  thf('216', plain, ($false),
% 0.40/0.62      inference('sat_resolution*', [status(thm)], ['1', '168', '169', '215'])).
% 0.40/0.62  
% 0.40/0.62  % SZS output end Refutation
% 0.40/0.62  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
