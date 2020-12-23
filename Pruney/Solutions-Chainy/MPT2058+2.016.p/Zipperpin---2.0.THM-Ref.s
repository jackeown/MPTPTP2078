%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sgnDE55E0z

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:51 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  255 ( 901 expanded)
%              Number of leaves         :   40 ( 296 expanded)
%              Depth                    :   36
%              Number of atoms          : 3231 (15830 expanded)
%              Number of equality atoms :   45 ( 236 expanded)
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

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('159',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('160',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','162'])).

thf('164',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['90'])).

thf('167',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('168',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('169',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('170',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['90'])).

thf('171',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('172',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('173',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('174',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('175',plain,(
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

thf('176',plain,(
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
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('180',plain,(
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
    inference('sup-',[status(thm)],['173','179'])).

thf('181',plain,(
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
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
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
    inference('sup-',[status(thm)],['172','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
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
    inference('sup-',[status(thm)],['171','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['170','185'])).

thf('187',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('190',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('191',plain,
    ( ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['188','191'])).

thf('193',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['169','192'])).

thf('194',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['136','146'])).

thf('197',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['168','198'])).

thf('200',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['201','202'])).

thf('204',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('207',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('210',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['167','209'])).

thf('211',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','165','166','212'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sgnDE55E0z
% 0.12/0.32  % Computer   : n009.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 20:47:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 175 iterations in 0.130s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.39/0.57  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.39/0.57  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.39/0.57  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.39/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.39/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.57  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.39/0.57  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.39/0.57  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.39/0.57  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.39/0.57  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.39/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.57  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.39/0.57  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.39/0.57  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.39/0.57  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.39/0.57  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.39/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.57  thf(t17_yellow19, conjecture,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.39/0.57             ( v1_subset_1 @
% 0.39/0.57               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.39/0.57             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.39/0.57             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.39/0.57             ( m1_subset_1 @
% 0.39/0.57               B @ 
% 0.39/0.57               ( k1_zfmisc_1 @
% 0.39/0.57                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.39/0.57           ( ![C:$i]:
% 0.39/0.57             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.57               ( ( r3_waybel_9 @
% 0.39/0.57                   A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.39/0.57                 ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i]:
% 0.39/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.39/0.57            ( l1_pre_topc @ A ) ) =>
% 0.39/0.57          ( ![B:$i]:
% 0.39/0.57            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.39/0.57                ( v1_subset_1 @
% 0.39/0.57                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.39/0.57                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.39/0.57                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.39/0.57                ( m1_subset_1 @
% 0.39/0.57                  B @ 
% 0.39/0.57                  ( k1_zfmisc_1 @
% 0.39/0.57                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.39/0.57              ( ![C:$i]:
% 0.39/0.57                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.57                  ( ( r3_waybel_9 @
% 0.39/0.57                      A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.39/0.57                    ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t17_yellow19])).
% 0.39/0.57  thf('0', plain,
% 0.39/0.57      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.39/0.57        | ~ (r3_waybel_9 @ sk_A @ 
% 0.39/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.39/0.57       ~
% 0.39/0.57       ((r3_waybel_9 @ sk_A @ 
% 0.39/0.57         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf(dt_l1_pre_topc, axiom,
% 0.39/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.39/0.57  thf('2', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.57  thf('3', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.57  thf('4', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.57  thf(dt_k2_subset_1, axiom,
% 0.39/0.57    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.39/0.57  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.39/0.57  thf('6', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.39/0.57  thf('7', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.39/0.57      inference('demod', [status(thm)], ['5', '6'])).
% 0.39/0.57  thf('8', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.57  thf(d3_struct_0, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X2 : $i]:
% 0.39/0.57         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_B @ 
% 0.39/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(d2_yellow_1, axiom,
% 0.39/0.57    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_B @ 
% 0.39/0.57        (k1_zfmisc_1 @ 
% 0.39/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.39/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (((m1_subset_1 @ sk_B @ 
% 0.39/0.57         (k1_zfmisc_1 @ 
% 0.39/0.57          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 0.39/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.57      inference('sup+', [status(thm)], ['9', '12'])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.57        | (m1_subset_1 @ sk_B @ 
% 0.39/0.57           (k1_zfmisc_1 @ 
% 0.39/0.57            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['8', '13'])).
% 0.39/0.57  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_B @ 
% 0.39/0.57        (k1_zfmisc_1 @ 
% 0.39/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.39/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.39/0.57  thf(fc5_yellow19, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.39/0.57         ( ~( v1_xboole_0 @ B ) ) & 
% 0.39/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.39/0.57         ( ~( v1_xboole_0 @ C ) ) & 
% 0.39/0.57         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.39/0.57         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.39/0.57         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.39/0.57         ( m1_subset_1 @
% 0.39/0.57           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.39/0.57       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.39/0.57         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.39/0.57         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.39/0.57          | (v1_xboole_0 @ X12)
% 0.39/0.57          | ~ (l1_struct_0 @ X13)
% 0.39/0.57          | (v2_struct_0 @ X13)
% 0.39/0.57          | (v1_xboole_0 @ X14)
% 0.39/0.57          | ~ (v1_subset_1 @ X14 @ (u1_struct_0 @ (k3_yellow_1 @ X12)))
% 0.39/0.57          | ~ (v2_waybel_0 @ X14 @ (k3_yellow_1 @ X12))
% 0.39/0.57          | ~ (v13_waybel_0 @ X14 @ (k3_yellow_1 @ X12))
% 0.39/0.57          | ~ (m1_subset_1 @ X14 @ 
% 0.39/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X12))))
% 0.39/0.57          | (v7_waybel_0 @ (k3_yellow19 @ X13 @ X12 @ X14)))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.39/0.57          | (v1_xboole_0 @ X12)
% 0.39/0.57          | ~ (l1_struct_0 @ X13)
% 0.39/0.57          | (v2_struct_0 @ X13)
% 0.39/0.57          | (v1_xboole_0 @ X14)
% 0.39/0.57          | ~ (v1_subset_1 @ X14 @ 
% 0.39/0.57               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X12))))
% 0.39/0.57          | ~ (v2_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.39/0.57          | ~ (v13_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.39/0.57          | ~ (m1_subset_1 @ X14 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X12)))))
% 0.39/0.57          | (v7_waybel_0 @ (k3_yellow19 @ X13 @ X12 @ X14)))),
% 0.39/0.57      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.57          | ~ (v13_waybel_0 @ sk_B @ 
% 0.39/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.39/0.57          | ~ (v2_waybel_0 @ sk_B @ 
% 0.39/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.39/0.57          | ~ (v1_subset_1 @ sk_B @ 
% 0.39/0.57               (u1_struct_0 @ 
% 0.39/0.57                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.39/0.57          | (v1_xboole_0 @ sk_B)
% 0.39/0.57          | (v2_struct_0 @ X0)
% 0.39/0.57          | ~ (l1_struct_0 @ X0)
% 0.39/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['16', '22'])).
% 0.39/0.57  thf('24', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (![X2 : $i]:
% 0.39/0.57         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.39/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.39/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (((v13_waybel_0 @ sk_B @ 
% 0.39/0.57         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.39/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.57      inference('sup+', [status(thm)], ['25', '28'])).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.57        | (v13_waybel_0 @ sk_B @ 
% 0.39/0.57           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['24', '29'])).
% 0.39/0.57  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.39/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.57      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.57  thf('33', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      (![X2 : $i]:
% 0.39/0.57         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('36', plain,
% 0.39/0.57      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.39/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.39/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      (((v2_waybel_0 @ sk_B @ 
% 0.39/0.57         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.39/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.57      inference('sup+', [status(thm)], ['34', '37'])).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.57        | (v2_waybel_0 @ sk_B @ 
% 0.39/0.57           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['33', '38'])).
% 0.39/0.57  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.39/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.39/0.57  thf('42', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.57  thf('43', plain,
% 0.39/0.57      (![X2 : $i]:
% 0.39/0.57         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.57  thf('44', plain,
% 0.39/0.57      ((v1_subset_1 @ sk_B @ 
% 0.39/0.57        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('45', plain,
% 0.39/0.57      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.57  thf('46', plain,
% 0.39/0.57      ((v1_subset_1 @ sk_B @ 
% 0.39/0.57        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.39/0.57      inference('demod', [status(thm)], ['44', '45'])).
% 0.39/0.57  thf('47', plain,
% 0.39/0.57      (((v1_subset_1 @ sk_B @ 
% 0.39/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.39/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.57      inference('sup+', [status(thm)], ['43', '46'])).
% 0.39/0.57  thf('48', plain,
% 0.39/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.57        | (v1_subset_1 @ sk_B @ 
% 0.39/0.57           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['42', '47'])).
% 0.39/0.57  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('50', plain,
% 0.39/0.57      ((v1_subset_1 @ sk_B @ 
% 0.39/0.57        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.39/0.57      inference('demod', [status(thm)], ['48', '49'])).
% 0.39/0.57  thf('51', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.57          | (v1_xboole_0 @ sk_B)
% 0.39/0.57          | (v2_struct_0 @ X0)
% 0.39/0.57          | ~ (l1_struct_0 @ X0)
% 0.39/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.39/0.57      inference('demod', [status(thm)], ['23', '32', '41', '50'])).
% 0.39/0.57  thf('52', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | (v1_xboole_0 @ sk_B)
% 0.39/0.57        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['7', '51'])).
% 0.39/0.57  thf('53', plain,
% 0.39/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.57        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.57        | (v1_xboole_0 @ sk_B)
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['4', '52'])).
% 0.39/0.57  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('55', plain,
% 0.39/0.57      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.57        | (v1_xboole_0 @ sk_B)
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['53', '54'])).
% 0.39/0.57  thf('56', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.57  thf('57', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.39/0.57      inference('demod', [status(thm)], ['5', '6'])).
% 0.39/0.57  thf('58', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_B @ 
% 0.39/0.57        (k1_zfmisc_1 @ 
% 0.39/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.39/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.39/0.57  thf(fc4_yellow19, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.39/0.57         ( ~( v1_xboole_0 @ B ) ) & 
% 0.39/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.39/0.57         ( ~( v1_xboole_0 @ C ) ) & 
% 0.39/0.57         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.39/0.57         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.39/0.57         ( m1_subset_1 @
% 0.39/0.57           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.39/0.57       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.39/0.57         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.39/0.57         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.39/0.57         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.39/0.57  thf('59', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.39/0.57          | (v1_xboole_0 @ X9)
% 0.39/0.57          | ~ (l1_struct_0 @ X10)
% 0.39/0.57          | (v2_struct_0 @ X10)
% 0.39/0.57          | (v1_xboole_0 @ X11)
% 0.39/0.57          | ~ (v2_waybel_0 @ X11 @ (k3_yellow_1 @ X9))
% 0.39/0.57          | ~ (v13_waybel_0 @ X11 @ (k3_yellow_1 @ X9))
% 0.39/0.57          | ~ (m1_subset_1 @ X11 @ 
% 0.39/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X9))))
% 0.39/0.57          | (v4_orders_2 @ (k3_yellow19 @ X10 @ X9 @ X11)))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.39/0.57  thf('60', plain,
% 0.39/0.57      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.57  thf('61', plain,
% 0.39/0.57      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.57  thf('62', plain,
% 0.39/0.57      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.57  thf('63', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.39/0.57          | (v1_xboole_0 @ X9)
% 0.39/0.57          | ~ (l1_struct_0 @ X10)
% 0.39/0.57          | (v2_struct_0 @ X10)
% 0.39/0.57          | (v1_xboole_0 @ X11)
% 0.39/0.57          | ~ (v2_waybel_0 @ X11 @ (k3_lattice3 @ (k1_lattice3 @ X9)))
% 0.39/0.57          | ~ (v13_waybel_0 @ X11 @ (k3_lattice3 @ (k1_lattice3 @ X9)))
% 0.39/0.57          | ~ (m1_subset_1 @ X11 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X9)))))
% 0.39/0.57          | (v4_orders_2 @ (k3_yellow19 @ X10 @ X9 @ X11)))),
% 0.39/0.57      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.39/0.57  thf('64', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.57          | ~ (v13_waybel_0 @ sk_B @ 
% 0.39/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.39/0.57          | ~ (v2_waybel_0 @ sk_B @ 
% 0.39/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.39/0.57          | (v1_xboole_0 @ sk_B)
% 0.39/0.57          | (v2_struct_0 @ X0)
% 0.39/0.57          | ~ (l1_struct_0 @ X0)
% 0.39/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['58', '63'])).
% 0.39/0.57  thf('65', plain,
% 0.39/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.39/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.57      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.57  thf('66', plain,
% 0.39/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.39/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.39/0.57  thf('67', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.57          | (v1_xboole_0 @ sk_B)
% 0.39/0.57          | (v2_struct_0 @ X0)
% 0.39/0.57          | ~ (l1_struct_0 @ X0)
% 0.39/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.39/0.57      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.39/0.57  thf('68', plain,
% 0.39/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | (v1_xboole_0 @ sk_B)
% 0.39/0.57        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['57', '67'])).
% 0.39/0.57  thf('69', plain,
% 0.39/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.57        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.57        | (v1_xboole_0 @ sk_B)
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['56', '68'])).
% 0.39/0.57  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('71', plain,
% 0.39/0.57      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.57        | (v1_xboole_0 @ sk_B)
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['69', '70'])).
% 0.39/0.57  thf('72', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.57  thf('73', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.39/0.57      inference('demod', [status(thm)], ['5', '6'])).
% 0.39/0.57  thf('74', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_B @ 
% 0.39/0.57        (k1_zfmisc_1 @ 
% 0.39/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.39/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.39/0.57  thf(dt_k3_yellow19, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.39/0.57         ( ~( v1_xboole_0 @ B ) ) & 
% 0.39/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.39/0.57         ( ~( v1_xboole_0 @ C ) ) & 
% 0.39/0.57         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.39/0.57         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.39/0.57         ( m1_subset_1 @
% 0.39/0.57           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.39/0.57       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.39/0.57         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.39/0.57         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.39/0.57  thf('75', plain,
% 0.39/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.39/0.57          | (v1_xboole_0 @ X6)
% 0.39/0.57          | ~ (l1_struct_0 @ X7)
% 0.39/0.57          | (v2_struct_0 @ X7)
% 0.39/0.57          | (v1_xboole_0 @ X8)
% 0.39/0.57          | ~ (v2_waybel_0 @ X8 @ (k3_yellow_1 @ X6))
% 0.39/0.57          | ~ (v13_waybel_0 @ X8 @ (k3_yellow_1 @ X6))
% 0.39/0.57          | ~ (m1_subset_1 @ X8 @ 
% 0.39/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X6))))
% 0.39/0.57          | (l1_waybel_0 @ (k3_yellow19 @ X7 @ X6 @ X8) @ X7))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.39/0.57  thf('76', plain,
% 0.39/0.57      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.57  thf('77', plain,
% 0.39/0.57      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.57  thf('78', plain,
% 0.39/0.57      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.57  thf('79', plain,
% 0.39/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.39/0.57          | (v1_xboole_0 @ X6)
% 0.39/0.57          | ~ (l1_struct_0 @ X7)
% 0.39/0.57          | (v2_struct_0 @ X7)
% 0.39/0.57          | (v1_xboole_0 @ X8)
% 0.39/0.57          | ~ (v2_waybel_0 @ X8 @ (k3_lattice3 @ (k1_lattice3 @ X6)))
% 0.39/0.57          | ~ (v13_waybel_0 @ X8 @ (k3_lattice3 @ (k1_lattice3 @ X6)))
% 0.39/0.57          | ~ (m1_subset_1 @ X8 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X6)))))
% 0.39/0.57          | (l1_waybel_0 @ (k3_yellow19 @ X7 @ X6 @ X8) @ X7))),
% 0.39/0.57      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.39/0.57  thf('80', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.39/0.58          | ~ (v13_waybel_0 @ sk_B @ 
% 0.39/0.58               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.39/0.58          | ~ (v2_waybel_0 @ sk_B @ 
% 0.39/0.58               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.39/0.58          | (v1_xboole_0 @ sk_B)
% 0.39/0.58          | (v2_struct_0 @ X0)
% 0.39/0.58          | ~ (l1_struct_0 @ X0)
% 0.39/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['74', '79'])).
% 0.39/0.58  thf('81', plain,
% 0.39/0.58      ((v13_waybel_0 @ sk_B @ 
% 0.39/0.58        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.58      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.58  thf('82', plain,
% 0.39/0.58      ((v2_waybel_0 @ sk_B @ 
% 0.39/0.58        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.39/0.58  thf('83', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.39/0.58          | (v1_xboole_0 @ sk_B)
% 0.39/0.58          | (v2_struct_0 @ X0)
% 0.39/0.58          | ~ (l1_struct_0 @ X0)
% 0.39/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.39/0.58      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.39/0.58  thf('84', plain,
% 0.39/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.39/0.58        | (v2_struct_0 @ sk_A)
% 0.39/0.58        | (v1_xboole_0 @ sk_B)
% 0.39/0.58        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.39/0.58           sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['73', '83'])).
% 0.39/0.58  thf('85', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.58        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.39/0.58           sk_A)
% 0.39/0.58        | (v1_xboole_0 @ sk_B)
% 0.39/0.58        | (v2_struct_0 @ sk_A)
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['72', '84'])).
% 0.39/0.58  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('87', plain,
% 0.39/0.58      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.39/0.58         sk_A)
% 0.39/0.58        | (v1_xboole_0 @ sk_B)
% 0.39/0.58        | (v2_struct_0 @ sk_A)
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['85', '86'])).
% 0.39/0.58  thf('88', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.58  thf('89', plain,
% 0.39/0.58      (![X2 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.58  thf('90', plain,
% 0.39/0.58      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.39/0.58        | (r3_waybel_9 @ sk_A @ 
% 0.39/0.58           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('91', plain,
% 0.39/0.58      (((r3_waybel_9 @ sk_A @ 
% 0.39/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.39/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('split', [status(esa)], ['90'])).
% 0.39/0.58  thf('92', plain,
% 0.39/0.58      ((((r3_waybel_9 @ sk_A @ 
% 0.39/0.58          (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.39/0.58         | ~ (l1_struct_0 @ sk_A)))
% 0.39/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['89', '91'])).
% 0.39/0.58  thf('93', plain,
% 0.39/0.58      (((~ (l1_pre_topc @ sk_A)
% 0.39/0.58         | (r3_waybel_9 @ sk_A @ 
% 0.39/0.58            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C)))
% 0.39/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['88', '92'])).
% 0.39/0.58  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('95', plain,
% 0.39/0.58      (((r3_waybel_9 @ sk_A @ 
% 0.39/0.58         (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.39/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['93', '94'])).
% 0.39/0.58  thf('96', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t12_yellow19, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.39/0.58             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.58               ( ( r3_waybel_9 @ A @ B @ C ) <=>
% 0.39/0.58                 ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.39/0.58  thf('97', plain,
% 0.39/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.58         ((v2_struct_0 @ X15)
% 0.39/0.58          | ~ (v4_orders_2 @ X15)
% 0.39/0.58          | ~ (v7_waybel_0 @ X15)
% 0.39/0.58          | ~ (l1_waybel_0 @ X15 @ X16)
% 0.39/0.58          | ~ (r3_waybel_9 @ X16 @ X15 @ X17)
% 0.39/0.58          | (r1_waybel_7 @ X16 @ (k2_yellow19 @ X16 @ X15) @ X17)
% 0.39/0.58          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.39/0.58          | ~ (l1_pre_topc @ X16)
% 0.39/0.58          | ~ (v2_pre_topc @ X16)
% 0.39/0.58          | (v2_struct_0 @ X16))),
% 0.39/0.58      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.39/0.58  thf('98', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v2_struct_0 @ sk_A)
% 0.39/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.39/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.58          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.39/0.58          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.39/0.58          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.39/0.58          | ~ (v7_waybel_0 @ X0)
% 0.39/0.58          | ~ (v4_orders_2 @ X0)
% 0.39/0.58          | (v2_struct_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['96', '97'])).
% 0.39/0.58  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('101', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v2_struct_0 @ sk_A)
% 0.39/0.58          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.39/0.58          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.39/0.58          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.39/0.58          | ~ (v7_waybel_0 @ X0)
% 0.39/0.58          | ~ (v4_orders_2 @ X0)
% 0.39/0.58          | (v2_struct_0 @ X0))),
% 0.39/0.58      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.39/0.58  thf('102', plain,
% 0.39/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58         | ~ (l1_waybel_0 @ 
% 0.39/0.58              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.39/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.39/0.58            (k2_yellow19 @ sk_A @ 
% 0.39/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.39/0.58            sk_C)
% 0.39/0.58         | (v2_struct_0 @ sk_A)))
% 0.39/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['95', '101'])).
% 0.39/0.58  thf('103', plain,
% 0.39/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.39/0.58            (k2_yellow19 @ sk_A @ 
% 0.39/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.39/0.58            sk_C)
% 0.39/0.58         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.39/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['87', '102'])).
% 0.39/0.58  thf('104', plain,
% 0.39/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.39/0.58            (k2_yellow19 @ sk_A @ 
% 0.39/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.39/0.58            sk_C)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['103'])).
% 0.39/0.58  thf('105', plain,
% 0.39/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.39/0.58            (k2_yellow19 @ sk_A @ 
% 0.39/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.39/0.58            sk_C)
% 0.39/0.58         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.39/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['71', '104'])).
% 0.39/0.58  thf('106', plain,
% 0.39/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.39/0.58            (k2_yellow19 @ sk_A @ 
% 0.39/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.39/0.58            sk_C)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['105'])).
% 0.39/0.58  thf('107', plain,
% 0.39/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.39/0.58            (k2_yellow19 @ sk_A @ 
% 0.39/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.39/0.58            sk_C)
% 0.39/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.39/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['55', '106'])).
% 0.39/0.58  thf('108', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.58  thf('109', plain,
% 0.39/0.58      (![X2 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.58  thf('110', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.58  thf('111', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_B @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.39/0.58      inference('demod', [status(thm)], ['10', '11'])).
% 0.39/0.58  thf(t15_yellow19, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.39/0.58             ( v1_subset_1 @
% 0.39/0.58               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.39/0.58             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.39/0.58             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.39/0.58             ( m1_subset_1 @
% 0.39/0.58               B @ 
% 0.39/0.58               ( k1_zfmisc_1 @
% 0.39/0.58                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.39/0.58           ( ( B ) =
% 0.39/0.58             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.39/0.58  thf('112', plain,
% 0.39/0.58      (![X18 : $i, X19 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ X18)
% 0.39/0.58          | ~ (v1_subset_1 @ X18 @ 
% 0.39/0.58               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X19))))
% 0.39/0.58          | ~ (v2_waybel_0 @ X18 @ (k3_yellow_1 @ (k2_struct_0 @ X19)))
% 0.39/0.58          | ~ (v13_waybel_0 @ X18 @ (k3_yellow_1 @ (k2_struct_0 @ X19)))
% 0.39/0.58          | ~ (m1_subset_1 @ X18 @ 
% 0.39/0.58               (k1_zfmisc_1 @ 
% 0.39/0.58                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X19)))))
% 0.39/0.58          | ((X18)
% 0.39/0.58              = (k2_yellow19 @ X19 @ 
% 0.39/0.58                 (k3_yellow19 @ X19 @ (k2_struct_0 @ X19) @ X18)))
% 0.39/0.58          | ~ (l1_struct_0 @ X19)
% 0.39/0.58          | (v2_struct_0 @ X19))),
% 0.39/0.58      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.39/0.58  thf('113', plain,
% 0.39/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.58  thf('114', plain,
% 0.39/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.58  thf('115', plain,
% 0.39/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.58  thf('116', plain,
% 0.39/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.58  thf('117', plain,
% 0.39/0.58      (![X18 : $i, X19 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ X18)
% 0.39/0.58          | ~ (v1_subset_1 @ X18 @ 
% 0.39/0.58               (u1_struct_0 @ 
% 0.39/0.58                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X19)))))
% 0.39/0.58          | ~ (v2_waybel_0 @ X18 @ 
% 0.39/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X19))))
% 0.39/0.58          | ~ (v13_waybel_0 @ X18 @ 
% 0.39/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X19))))
% 0.39/0.58          | ~ (m1_subset_1 @ X18 @ 
% 0.39/0.58               (k1_zfmisc_1 @ 
% 0.39/0.58                (u1_struct_0 @ 
% 0.39/0.58                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X19))))))
% 0.39/0.58          | ((X18)
% 0.39/0.58              = (k2_yellow19 @ X19 @ 
% 0.39/0.58                 (k3_yellow19 @ X19 @ (k2_struct_0 @ X19) @ X18)))
% 0.39/0.58          | ~ (l1_struct_0 @ X19)
% 0.39/0.58          | (v2_struct_0 @ X19))),
% 0.39/0.58      inference('demod', [status(thm)], ['112', '113', '114', '115', '116'])).
% 0.39/0.58  thf('118', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_A)
% 0.39/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.39/0.58        | ((sk_B)
% 0.39/0.58            = (k2_yellow19 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.39/0.58        | ~ (v13_waybel_0 @ sk_B @ 
% 0.39/0.58             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.39/0.58        | ~ (v2_waybel_0 @ sk_B @ 
% 0.39/0.58             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.39/0.58        | ~ (v1_subset_1 @ sk_B @ 
% 0.39/0.58             (u1_struct_0 @ 
% 0.39/0.58              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.39/0.58        | (v1_xboole_0 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['111', '117'])).
% 0.39/0.58  thf('119', plain,
% 0.39/0.58      ((v13_waybel_0 @ sk_B @ 
% 0.39/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.39/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.39/0.58  thf('120', plain,
% 0.39/0.58      ((v2_waybel_0 @ sk_B @ 
% 0.39/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.39/0.58      inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.58  thf('121', plain,
% 0.39/0.58      ((v1_subset_1 @ sk_B @ 
% 0.39/0.58        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.39/0.58      inference('demod', [status(thm)], ['44', '45'])).
% 0.39/0.58  thf('122', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_A)
% 0.39/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.39/0.58        | ((sk_B)
% 0.39/0.58            = (k2_yellow19 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.39/0.58        | (v1_xboole_0 @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['118', '119', '120', '121'])).
% 0.39/0.58  thf('123', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.58        | (v1_xboole_0 @ sk_B)
% 0.39/0.58        | ((sk_B)
% 0.39/0.58            = (k2_yellow19 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.39/0.58        | (v2_struct_0 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['110', '122'])).
% 0.39/0.58  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('125', plain,
% 0.39/0.58      (((v1_xboole_0 @ sk_B)
% 0.39/0.58        | ((sk_B)
% 0.39/0.58            = (k2_yellow19 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.39/0.58        | (v2_struct_0 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['123', '124'])).
% 0.39/0.58  thf('126', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('127', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_A)
% 0.39/0.58        | ((sk_B)
% 0.39/0.58            = (k2_yellow19 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.39/0.58      inference('clc', [status(thm)], ['125', '126'])).
% 0.39/0.58  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('129', plain,
% 0.39/0.58      (((sk_B)
% 0.39/0.58         = (k2_yellow19 @ sk_A @ 
% 0.39/0.58            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.39/0.58      inference('clc', [status(thm)], ['127', '128'])).
% 0.39/0.58  thf('130', plain,
% 0.39/0.58      ((((sk_B)
% 0.39/0.58          = (k2_yellow19 @ sk_A @ 
% 0.39/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.39/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.58      inference('sup+', [status(thm)], ['109', '129'])).
% 0.39/0.58  thf('131', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.58        | ((sk_B)
% 0.39/0.58            = (k2_yellow19 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['108', '130'])).
% 0.39/0.58  thf('132', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('133', plain,
% 0.39/0.58      (((sk_B)
% 0.39/0.58         = (k2_yellow19 @ sk_A @ 
% 0.39/0.58            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.39/0.58      inference('demod', [status(thm)], ['131', '132'])).
% 0.39/0.58  thf('134', plain,
% 0.39/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.39/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.39/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['107', '133'])).
% 0.39/0.58  thf('135', plain,
% 0.39/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['134'])).
% 0.39/0.58  thf('136', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.39/0.58      inference('demod', [status(thm)], ['5', '6'])).
% 0.39/0.58  thf('137', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_B @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.39/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.39/0.58  thf('138', plain,
% 0.39/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.39/0.58          | (v1_xboole_0 @ X6)
% 0.39/0.58          | ~ (l1_struct_0 @ X7)
% 0.39/0.58          | (v2_struct_0 @ X7)
% 0.39/0.58          | (v1_xboole_0 @ X8)
% 0.39/0.58          | ~ (v2_waybel_0 @ X8 @ (k3_yellow_1 @ X6))
% 0.39/0.58          | ~ (v13_waybel_0 @ X8 @ (k3_yellow_1 @ X6))
% 0.39/0.58          | ~ (m1_subset_1 @ X8 @ 
% 0.39/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X6))))
% 0.39/0.58          | ~ (v2_struct_0 @ (k3_yellow19 @ X7 @ X6 @ X8)))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.39/0.58  thf('139', plain,
% 0.39/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.58  thf('140', plain,
% 0.39/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.58  thf('141', plain,
% 0.39/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.58  thf('142', plain,
% 0.39/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.39/0.58          | (v1_xboole_0 @ X6)
% 0.39/0.58          | ~ (l1_struct_0 @ X7)
% 0.39/0.58          | (v2_struct_0 @ X7)
% 0.39/0.58          | (v1_xboole_0 @ X8)
% 0.39/0.58          | ~ (v2_waybel_0 @ X8 @ (k3_lattice3 @ (k1_lattice3 @ X6)))
% 0.39/0.58          | ~ (v13_waybel_0 @ X8 @ (k3_lattice3 @ (k1_lattice3 @ X6)))
% 0.39/0.58          | ~ (m1_subset_1 @ X8 @ 
% 0.39/0.58               (k1_zfmisc_1 @ 
% 0.39/0.58                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X6)))))
% 0.39/0.58          | ~ (v2_struct_0 @ (k3_yellow19 @ X7 @ X6 @ X8)))),
% 0.39/0.58      inference('demod', [status(thm)], ['138', '139', '140', '141'])).
% 0.39/0.58  thf('143', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58          | ~ (v13_waybel_0 @ sk_B @ 
% 0.39/0.58               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.39/0.58          | ~ (v2_waybel_0 @ sk_B @ 
% 0.39/0.58               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.39/0.58          | (v1_xboole_0 @ sk_B)
% 0.39/0.58          | (v2_struct_0 @ X0)
% 0.39/0.58          | ~ (l1_struct_0 @ X0)
% 0.39/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['137', '142'])).
% 0.39/0.58  thf('144', plain,
% 0.39/0.58      ((v13_waybel_0 @ sk_B @ 
% 0.39/0.58        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.58      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.58  thf('145', plain,
% 0.39/0.58      ((v2_waybel_0 @ sk_B @ 
% 0.39/0.58        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.39/0.58  thf('146', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58          | (v1_xboole_0 @ sk_B)
% 0.39/0.58          | (v2_struct_0 @ X0)
% 0.39/0.58          | ~ (l1_struct_0 @ X0)
% 0.39/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.39/0.58      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.39/0.58  thf('147', plain,
% 0.39/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.39/0.58        | (v2_struct_0 @ sk_A)
% 0.39/0.58        | (v1_xboole_0 @ sk_B)
% 0.39/0.58        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['136', '146'])).
% 0.39/0.58  thf('148', plain,
% 0.39/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | ~ (l1_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['135', '147'])).
% 0.39/0.58  thf('149', plain,
% 0.39/0.58      (((~ (l1_struct_0 @ sk_A)
% 0.39/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['148'])).
% 0.39/0.58  thf('150', plain,
% 0.39/0.58      (((~ (l1_pre_topc @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.39/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['3', '149'])).
% 0.39/0.58  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('152', plain,
% 0.39/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.39/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['150', '151'])).
% 0.39/0.58  thf('153', plain,
% 0.39/0.58      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.39/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.58      inference('split', [status(esa)], ['0'])).
% 0.39/0.58  thf('154', plain,
% 0.39/0.58      ((((v1_xboole_0 @ sk_B)
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['152', '153'])).
% 0.39/0.58  thf('155', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('156', plain,
% 0.39/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.39/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('clc', [status(thm)], ['154', '155'])).
% 0.39/0.58  thf('157', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('158', plain,
% 0.39/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.39/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('clc', [status(thm)], ['156', '157'])).
% 0.39/0.58  thf(fc2_struct_0, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.39/0.58       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.39/0.58  thf('159', plain,
% 0.39/0.58      (![X4 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ (u1_struct_0 @ X4))
% 0.39/0.58          | ~ (l1_struct_0 @ X4)
% 0.39/0.58          | (v2_struct_0 @ X4))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.39/0.58  thf('160', plain,
% 0.39/0.58      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.39/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['158', '159'])).
% 0.39/0.58  thf('161', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('162', plain,
% 0.39/0.58      ((~ (l1_struct_0 @ sk_A))
% 0.39/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('clc', [status(thm)], ['160', '161'])).
% 0.39/0.58  thf('163', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_A))
% 0.39/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['2', '162'])).
% 0.39/0.58  thf('164', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('165', plain,
% 0.39/0.58      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.39/0.58       ~
% 0.39/0.58       ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['163', '164'])).
% 0.39/0.58  thf('166', plain,
% 0.39/0.58      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.39/0.58       ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.39/0.58      inference('split', [status(esa)], ['90'])).
% 0.39/0.58  thf('167', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.58  thf('168', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.58  thf('169', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.58  thf('170', plain,
% 0.39/0.58      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.39/0.58         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.58      inference('split', [status(esa)], ['90'])).
% 0.39/0.58  thf('171', plain,
% 0.39/0.58      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58        | (v1_xboole_0 @ sk_B)
% 0.39/0.58        | (v2_struct_0 @ sk_A)
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['69', '70'])).
% 0.39/0.58  thf('172', plain,
% 0.39/0.58      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58        | (v1_xboole_0 @ sk_B)
% 0.39/0.58        | (v2_struct_0 @ sk_A)
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['53', '54'])).
% 0.39/0.58  thf('173', plain,
% 0.39/0.58      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.39/0.58         sk_A)
% 0.39/0.58        | (v1_xboole_0 @ sk_B)
% 0.39/0.58        | (v2_struct_0 @ sk_A)
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['85', '86'])).
% 0.39/0.58  thf('174', plain,
% 0.39/0.58      (((sk_B)
% 0.39/0.58         = (k2_yellow19 @ sk_A @ 
% 0.39/0.58            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.39/0.58      inference('demod', [status(thm)], ['131', '132'])).
% 0.39/0.58  thf('175', plain,
% 0.39/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.58         ((v2_struct_0 @ X15)
% 0.39/0.58          | ~ (v4_orders_2 @ X15)
% 0.39/0.58          | ~ (v7_waybel_0 @ X15)
% 0.39/0.58          | ~ (l1_waybel_0 @ X15 @ X16)
% 0.39/0.58          | ~ (r1_waybel_7 @ X16 @ (k2_yellow19 @ X16 @ X15) @ X17)
% 0.39/0.58          | (r3_waybel_9 @ X16 @ X15 @ X17)
% 0.39/0.58          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.39/0.58          | ~ (l1_pre_topc @ X16)
% 0.39/0.58          | ~ (v2_pre_topc @ X16)
% 0.39/0.58          | (v2_struct_0 @ X16))),
% 0.39/0.58      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.39/0.58  thf('176', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.39/0.58          | (v2_struct_0 @ sk_A)
% 0.39/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.39/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.39/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.39/0.58          | ~ (l1_waybel_0 @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.39/0.58          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['174', '175'])).
% 0.39/0.58  thf('177', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('178', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('179', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.39/0.58          | (v2_struct_0 @ sk_A)
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.39/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.39/0.58          | ~ (l1_waybel_0 @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.39/0.58          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.39/0.58      inference('demod', [status(thm)], ['176', '177', '178'])).
% 0.39/0.58  thf('180', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | (v2_struct_0 @ sk_A)
% 0.39/0.58          | (v1_xboole_0 @ sk_B)
% 0.39/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.39/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | (v2_struct_0 @ sk_A)
% 0.39/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['173', '179'])).
% 0.39/0.58  thf('181', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.39/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.39/0.58          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58          | (v1_xboole_0 @ sk_B)
% 0.39/0.58          | (v2_struct_0 @ sk_A)
% 0.39/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['180'])).
% 0.39/0.58  thf('182', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | (v2_struct_0 @ sk_A)
% 0.39/0.58          | (v1_xboole_0 @ sk_B)
% 0.39/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | (v2_struct_0 @ sk_A)
% 0.39/0.58          | (v1_xboole_0 @ sk_B)
% 0.39/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.39/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['172', '181'])).
% 0.39/0.58  thf('183', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.39/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.39/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58          | (v1_xboole_0 @ sk_B)
% 0.39/0.58          | (v2_struct_0 @ sk_A)
% 0.39/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['182'])).
% 0.39/0.58  thf('184', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | (v2_struct_0 @ sk_A)
% 0.39/0.58          | (v1_xboole_0 @ sk_B)
% 0.39/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | (v2_struct_0 @ sk_A)
% 0.39/0.58          | (v1_xboole_0 @ sk_B)
% 0.39/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.39/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['171', '183'])).
% 0.39/0.58  thf('185', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.39/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.39/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58          | (v1_xboole_0 @ sk_B)
% 0.39/0.58          | (v2_struct_0 @ sk_A)
% 0.39/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['184'])).
% 0.39/0.58  thf('186', plain,
% 0.39/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58         | (r3_waybel_9 @ sk_A @ 
% 0.39/0.58            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.39/0.58         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))))
% 0.39/0.58         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['170', '185'])).
% 0.39/0.58  thf('187', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('188', plain,
% 0.39/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58         | (r3_waybel_9 @ sk_A @ 
% 0.39/0.58            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C)))
% 0.39/0.58         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['186', '187'])).
% 0.39/0.58  thf('189', plain,
% 0.39/0.58      (![X2 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.58  thf('190', plain,
% 0.39/0.58      ((~ (r3_waybel_9 @ sk_A @ 
% 0.39/0.58           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('split', [status(esa)], ['0'])).
% 0.39/0.58  thf('191', plain,
% 0.39/0.58      (((~ (r3_waybel_9 @ sk_A @ 
% 0.39/0.58            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.39/0.58         | ~ (l1_struct_0 @ sk_A)))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['189', '190'])).
% 0.39/0.58  thf('192', plain,
% 0.39/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58         | ~ (l1_struct_0 @ sk_A)))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.39/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['188', '191'])).
% 0.39/0.58  thf('193', plain,
% 0.39/0.58      (((~ (l1_pre_topc @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.39/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['169', '192'])).
% 0.39/0.58  thf('194', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('195', plain,
% 0.39/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.39/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['193', '194'])).
% 0.39/0.58  thf('196', plain,
% 0.39/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.39/0.58        | (v2_struct_0 @ sk_A)
% 0.39/0.58        | (v1_xboole_0 @ sk_B)
% 0.39/0.58        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['136', '146'])).
% 0.39/0.58  thf('197', plain,
% 0.39/0.58      ((((v1_xboole_0 @ sk_B)
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | ~ (l1_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.39/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['195', '196'])).
% 0.39/0.58  thf('198', plain,
% 0.39/0.58      (((~ (l1_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.39/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['197'])).
% 0.39/0.58  thf('199', plain,
% 0.39/0.58      (((~ (l1_pre_topc @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ sk_B)
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.39/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['168', '198'])).
% 0.39/0.58  thf('200', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('201', plain,
% 0.39/0.58      ((((v1_xboole_0 @ sk_B)
% 0.39/0.58         | (v2_struct_0 @ sk_A)
% 0.39/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.39/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['199', '200'])).
% 0.39/0.58  thf('202', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('203', plain,
% 0.39/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.39/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.58      inference('clc', [status(thm)], ['201', '202'])).
% 0.39/0.58  thf('204', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('205', plain,
% 0.39/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.39/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.58      inference('clc', [status(thm)], ['203', '204'])).
% 0.39/0.58  thf('206', plain,
% 0.39/0.58      (![X4 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ (u1_struct_0 @ X4))
% 0.39/0.58          | ~ (l1_struct_0 @ X4)
% 0.39/0.58          | (v2_struct_0 @ X4))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.39/0.58  thf('207', plain,
% 0.39/0.58      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.39/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['205', '206'])).
% 0.39/0.58  thf('208', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('209', plain,
% 0.39/0.58      ((~ (l1_struct_0 @ sk_A))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.39/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.58      inference('clc', [status(thm)], ['207', '208'])).
% 0.39/0.58  thf('210', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_A))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.39/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['167', '209'])).
% 0.39/0.58  thf('211', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('212', plain,
% 0.39/0.58      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.39/0.58       ((r3_waybel_9 @ sk_A @ 
% 0.39/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['210', '211'])).
% 0.39/0.58  thf('213', plain, ($false),
% 0.39/0.58      inference('sat_resolution*', [status(thm)], ['1', '165', '166', '212'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
