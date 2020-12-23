%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2CWB0EMvIz

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  286 ( 938 expanded)
%              Number of leaves         :   41 ( 308 expanded)
%              Depth                    :   42
%              Number of atoms          : 3797 (16231 expanded)
%              Number of equality atoms :   51 ( 249 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7 = X6 )
      | ( v1_subset_1 @ X7 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( k2_subset_1 @ X0 ) @ X0 )
      | ( ( k2_subset_1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('9',plain,(
    ! [X1: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X1 ) @ X1 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('13',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

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

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v1_xboole_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v1_subset_1 @ X16 @ ( u1_struct_0 @ ( k3_yellow_1 @ X14 ) ) )
      | ~ ( v2_waybel_0 @ X16 @ ( k3_yellow_1 @ X14 ) )
      | ~ ( v13_waybel_0 @ X16 @ ( k3_yellow_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X14 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X15 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('22',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('23',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('24',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('25',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v1_xboole_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v1_subset_1 @ X16 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X14 ) ) ) )
      | ~ ( v2_waybel_0 @ X16 @ ( k3_lattice3 @ ( k1_lattice3 @ X14 ) ) )
      | ~ ( v13_waybel_0 @ X16 @ ( k3_lattice3 @ ( k1_lattice3 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X14 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X15 @ X14 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,(
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
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('29',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('32',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('38',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('41',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('47',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('48',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('50',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['27','36','45','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','55'])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('61',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

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

thf('63',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v2_waybel_0 @ X13 @ ( k3_yellow_1 @ X11 ) )
      | ~ ( v13_waybel_0 @ X13 @ ( k3_yellow_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X11 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X12 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('64',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('65',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('66',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('67',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v2_waybel_0 @ X13 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) )
      | ~ ( v13_waybel_0 @ X13 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X12 @ X11 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('70',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','71'])).

thf('73',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('77',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

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

thf('79',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_xboole_0 @ X8 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v2_waybel_0 @ X10 @ ( k3_yellow_1 @ X8 ) )
      | ~ ( v13_waybel_0 @ X10 @ ( k3_yellow_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X8 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X9 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('80',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('81',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('82',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('83',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_xboole_0 @ X8 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v2_waybel_0 @ X10 @ ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) )
      | ~ ( v13_waybel_0 @ X10 @ ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X9 @ X8 @ X10 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('86',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['77','87'])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('93',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('94',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['94'])).

thf('96',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['93','95'])).

thf('97',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['92','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
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

thf('101',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X18 )
      | ~ ( r3_waybel_9 @ X18 @ X17 @ X19 )
      | ( r1_waybel_7 @ X18 @ ( k2_yellow19 @ X18 @ X17 ) @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('102',plain,(
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
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['99','105'])).

thf('107',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['91','106'])).

thf('108',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
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
    inference('sup-',[status(thm)],['75','108'])).

thf('110',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('111',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('112',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('113',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

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

thf('114',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( v1_subset_1 @ X20 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X21 ) ) ) )
      | ~ ( v2_waybel_0 @ X20 @ ( k3_yellow_1 @ ( k2_struct_0 @ X21 ) ) )
      | ~ ( v13_waybel_0 @ X20 @ ( k3_yellow_1 @ ( k2_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X21 ) ) ) ) )
      | ( X20
        = ( k2_yellow19 @ X21 @ ( k3_yellow19 @ X21 @ ( k2_struct_0 @ X21 ) @ X20 ) ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

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
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('118',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('119',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( v1_subset_1 @ X20 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X21 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X20 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X21 ) ) ) )
      | ~ ( v13_waybel_0 @ X20 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X21 ) ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X21 ) ) ) ) ) )
      | ( X20
        = ( k2_yellow19 @ X21 @ ( k3_yellow19 @ X21 @ ( k2_struct_0 @ X21 ) @ X20 ) ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['113','119'])).

thf('121',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('122',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('123',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['120','121','122','123'])).

thf('125',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['112','124'])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['111','131'])).

thf('133',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['110','132'])).

thf('134',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
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
    inference(demod,[status(thm)],['109','135'])).

thf('137',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['59','137'])).

thf('139',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('141',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('142',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_xboole_0 @ X8 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v2_waybel_0 @ X10 @ ( k3_yellow_1 @ X8 ) )
      | ~ ( v13_waybel_0 @ X10 @ ( k3_yellow_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X8 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X9 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('143',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('144',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('145',plain,(
    ! [X5: $i] :
      ( ( k3_yellow_1 @ X5 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('146',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_xboole_0 @ X8 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v2_waybel_0 @ X10 @ ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) )
      | ~ ( v13_waybel_0 @ X10 @ ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X9 @ X8 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['142','143','144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['141','146'])).

thf('148',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('149',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['140','150'])).

thf('152',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['139','151'])).

thf('153',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['3','153'])).

thf('155',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('158',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['160','161'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('163',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('164',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

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
    inference(split,[status(esa)],['94'])).

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

thf('173',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('174',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('175',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['94'])).

thf('176',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('177',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('178',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('179',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('180',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('181',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('182',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('183',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('184',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X18 )
      | ~ ( r1_waybel_7 @ X18 @ ( k2_yellow19 @ X18 @ X17 ) @ X19 )
      | ( r3_waybel_9 @ X18 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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
    inference(demod,[status(thm)],['5','10'])).

thf('209',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('210',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('211',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('212',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_xboole_0 @ X8 )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v2_waybel_0 @ X10 @ ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) )
      | ~ ( v13_waybel_0 @ X10 @ ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X8 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X9 @ X8 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['142','143','144','145'])).

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
    inference(demod,[status(thm)],['30','31'])).

thf('215',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

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
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('237',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
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
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2CWB0EMvIz
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:32:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 188 iterations in 0.101s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.58  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.58  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 0.21/0.58  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.21/0.58  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.58  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.58  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.21/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.58  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.21/0.58  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.21/0.58  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.21/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.58  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.21/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.58  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.58  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.21/0.58  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.58  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.21/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.58  thf(t17_yellow19, conjecture,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.58             ( v1_subset_1 @
% 0.21/0.58               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.58             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.58             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.58             ( m1_subset_1 @
% 0.21/0.58               B @ 
% 0.21/0.58               ( k1_zfmisc_1 @
% 0.21/0.58                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.58           ( ![C:$i]:
% 0.21/0.58             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.58               ( ( r3_waybel_9 @
% 0.21/0.58                   A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.21/0.58                 ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i]:
% 0.21/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.58            ( l1_pre_topc @ A ) ) =>
% 0.21/0.58          ( ![B:$i]:
% 0.21/0.58            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.58                ( v1_subset_1 @
% 0.21/0.58                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.58                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.58                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.58                ( m1_subset_1 @
% 0.21/0.58                  B @ 
% 0.21/0.58                  ( k1_zfmisc_1 @
% 0.21/0.58                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.58              ( ![C:$i]:
% 0.21/0.58                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.58                  ( ( r3_waybel_9 @
% 0.21/0.58                      A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.21/0.58                    ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t17_yellow19])).
% 0.21/0.58  thf('0', plain,
% 0.21/0.58      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.21/0.58        | ~ (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('1', plain,
% 0.21/0.58      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.21/0.58       ~
% 0.21/0.58       ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf(dt_l1_pre_topc, axiom,
% 0.21/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.58  thf('2', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('3', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('4', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf(dt_k2_subset_1, axiom,
% 0.21/0.58    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      (![X0 : $i]: (m1_subset_1 @ (k2_subset_1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.58  thf('6', plain,
% 0.21/0.58      (![X0 : $i]: (m1_subset_1 @ (k2_subset_1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.58  thf(d7_subset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.58       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.21/0.58  thf('7', plain,
% 0.21/0.58      (![X6 : $i, X7 : $i]:
% 0.21/0.58         (((X7) = (X6))
% 0.21/0.58          | (v1_subset_1 @ X7 @ X6)
% 0.21/0.58          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v1_subset_1 @ (k2_subset_1 @ X0) @ X0) | ((k2_subset_1 @ X0) = (X0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.58  thf(fc14_subset_1, axiom,
% 0.21/0.58    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.21/0.58  thf('9', plain, (![X1 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X1) @ X1)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.21/0.58  thf('10', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.21/0.58      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.58  thf('11', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.58      inference('demod', [status(thm)], ['5', '10'])).
% 0.21/0.58  thf('12', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf(d3_struct_0, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (![X2 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ 
% 0.21/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(d2_yellow_1, axiom,
% 0.21/0.58    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (((m1_subset_1 @ sk_B @ 
% 0.21/0.58         (k1_zfmisc_1 @ 
% 0.21/0.58          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup+', [status(thm)], ['13', '16'])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | (m1_subset_1 @ sk_B @ 
% 0.21/0.58           (k1_zfmisc_1 @ 
% 0.21/0.58            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['12', '17'])).
% 0.21/0.58  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('20', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.21/0.58      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.58  thf(fc5_yellow19, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.58         ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.58         ( ~( v1_xboole_0 @ C ) ) & 
% 0.21/0.58         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.21/0.58         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.58         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.58         ( m1_subset_1 @
% 0.21/0.58           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.21/0.58       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.21/0.58         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.21/0.58         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.21/0.58  thf('21', plain,
% 0.21/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.58          | (v1_xboole_0 @ X14)
% 0.21/0.58          | ~ (l1_struct_0 @ X15)
% 0.21/0.58          | (v2_struct_0 @ X15)
% 0.21/0.58          | (v1_xboole_0 @ X16)
% 0.21/0.58          | ~ (v1_subset_1 @ X16 @ (u1_struct_0 @ (k3_yellow_1 @ X14)))
% 0.21/0.58          | ~ (v2_waybel_0 @ X16 @ (k3_yellow_1 @ X14))
% 0.21/0.58          | ~ (v13_waybel_0 @ X16 @ (k3_yellow_1 @ X14))
% 0.21/0.58          | ~ (m1_subset_1 @ X16 @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X14))))
% 0.21/0.58          | (v7_waybel_0 @ (k3_yellow19 @ X15 @ X14 @ X16)))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('24', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('26', plain,
% 0.21/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.58          | (v1_xboole_0 @ X14)
% 0.21/0.58          | ~ (l1_struct_0 @ X15)
% 0.21/0.58          | (v2_struct_0 @ X15)
% 0.21/0.58          | (v1_xboole_0 @ X16)
% 0.21/0.58          | ~ (v1_subset_1 @ X16 @ 
% 0.21/0.58               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X14))))
% 0.21/0.58          | ~ (v2_waybel_0 @ X16 @ (k3_lattice3 @ (k1_lattice3 @ X14)))
% 0.21/0.58          | ~ (v13_waybel_0 @ X16 @ (k3_lattice3 @ (k1_lattice3 @ X14)))
% 0.21/0.58          | ~ (m1_subset_1 @ X16 @ 
% 0.21/0.58               (k1_zfmisc_1 @ 
% 0.21/0.58                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X14)))))
% 0.21/0.58          | (v7_waybel_0 @ (k3_yellow19 @ X15 @ X14 @ X16)))),
% 0.21/0.58      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.21/0.58  thf('27', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | ~ (v13_waybel_0 @ sk_B @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58          | ~ (v2_waybel_0 @ sk_B @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58          | ~ (v1_subset_1 @ sk_B @ 
% 0.21/0.58               (u1_struct_0 @ 
% 0.21/0.58                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['20', '26'])).
% 0.21/0.58  thf('28', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('29', plain,
% 0.21/0.58      (![X2 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('31', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('32', plain,
% 0.21/0.58      ((v13_waybel_0 @ sk_B @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.58  thf('33', plain,
% 0.21/0.58      (((v13_waybel_0 @ sk_B @ 
% 0.21/0.58         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup+', [status(thm)], ['29', '32'])).
% 0.21/0.58  thf('34', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | (v13_waybel_0 @ sk_B @ 
% 0.21/0.58           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['28', '33'])).
% 0.21/0.58  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('36', plain,
% 0.21/0.58      ((v13_waybel_0 @ sk_B @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.58  thf('37', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('38', plain,
% 0.21/0.58      (![X2 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('39', plain,
% 0.21/0.58      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('40', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('41', plain,
% 0.21/0.58      ((v2_waybel_0 @ sk_B @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.58  thf('42', plain,
% 0.21/0.58      (((v2_waybel_0 @ sk_B @ 
% 0.21/0.58         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup+', [status(thm)], ['38', '41'])).
% 0.21/0.58  thf('43', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | (v2_waybel_0 @ sk_B @ 
% 0.21/0.58           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['37', '42'])).
% 0.21/0.58  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('45', plain,
% 0.21/0.58      ((v2_waybel_0 @ sk_B @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.58  thf('46', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('47', plain,
% 0.21/0.58      (![X2 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('48', plain,
% 0.21/0.58      ((v1_subset_1 @ sk_B @ 
% 0.21/0.58        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('49', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('50', plain,
% 0.21/0.58      ((v1_subset_1 @ sk_B @ 
% 0.21/0.58        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.58      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.58  thf('51', plain,
% 0.21/0.58      (((v1_subset_1 @ sk_B @ 
% 0.21/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup+', [status(thm)], ['47', '50'])).
% 0.21/0.58  thf('52', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | (v1_subset_1 @ sk_B @ 
% 0.21/0.58           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['46', '51'])).
% 0.21/0.58  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('54', plain,
% 0.21/0.58      ((v1_subset_1 @ sk_B @ 
% 0.21/0.58        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.58      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.58  thf('55', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['27', '36', '45', '54'])).
% 0.21/0.58  thf('56', plain,
% 0.21/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B)
% 0.21/0.58        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['11', '55'])).
% 0.21/0.58  thf('57', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58        | (v1_xboole_0 @ sk_B)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['4', '56'])).
% 0.21/0.58  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('59', plain,
% 0.21/0.58      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58        | (v1_xboole_0 @ sk_B)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.58  thf('60', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('61', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.58      inference('demod', [status(thm)], ['5', '10'])).
% 0.21/0.58  thf('62', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.21/0.58      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.58  thf(fc4_yellow19, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.58         ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.58         ( ~( v1_xboole_0 @ C ) ) & 
% 0.21/0.58         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.58         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.58         ( m1_subset_1 @
% 0.21/0.58           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.21/0.58       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.21/0.58         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.21/0.58         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.21/0.58         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.21/0.58  thf('63', plain,
% 0.21/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.58          | (v1_xboole_0 @ X11)
% 0.21/0.58          | ~ (l1_struct_0 @ X12)
% 0.21/0.58          | (v2_struct_0 @ X12)
% 0.21/0.58          | (v1_xboole_0 @ X13)
% 0.21/0.58          | ~ (v2_waybel_0 @ X13 @ (k3_yellow_1 @ X11))
% 0.21/0.58          | ~ (v13_waybel_0 @ X13 @ (k3_yellow_1 @ X11))
% 0.21/0.58          | ~ (m1_subset_1 @ X13 @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X11))))
% 0.21/0.58          | (v4_orders_2 @ (k3_yellow19 @ X12 @ X11 @ X13)))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.21/0.58  thf('64', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('65', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('66', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('67', plain,
% 0.21/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.58          | (v1_xboole_0 @ X11)
% 0.21/0.58          | ~ (l1_struct_0 @ X12)
% 0.21/0.58          | (v2_struct_0 @ X12)
% 0.21/0.58          | (v1_xboole_0 @ X13)
% 0.21/0.58          | ~ (v2_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.21/0.58          | ~ (v13_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.21/0.58          | ~ (m1_subset_1 @ X13 @ 
% 0.21/0.58               (k1_zfmisc_1 @ 
% 0.21/0.58                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X11)))))
% 0.21/0.58          | (v4_orders_2 @ (k3_yellow19 @ X12 @ X11 @ X13)))),
% 0.21/0.58      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 0.21/0.58  thf('68', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | ~ (v13_waybel_0 @ sk_B @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58          | ~ (v2_waybel_0 @ sk_B @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['62', '67'])).
% 0.21/0.58  thf('69', plain,
% 0.21/0.58      ((v13_waybel_0 @ sk_B @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.58  thf('70', plain,
% 0.21/0.58      ((v2_waybel_0 @ sk_B @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.58  thf('71', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.21/0.58  thf('72', plain,
% 0.21/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B)
% 0.21/0.58        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['61', '71'])).
% 0.21/0.58  thf('73', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58        | (v1_xboole_0 @ sk_B)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['60', '72'])).
% 0.21/0.58  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('75', plain,
% 0.21/0.58      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58        | (v1_xboole_0 @ sk_B)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.58  thf('76', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('77', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.58      inference('demod', [status(thm)], ['5', '10'])).
% 0.21/0.58  thf('78', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.21/0.58      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.58  thf(dt_k3_yellow19, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.58         ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.58         ( ~( v1_xboole_0 @ C ) ) & 
% 0.21/0.58         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.58         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.58         ( m1_subset_1 @
% 0.21/0.58           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.21/0.58       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.21/0.58         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.21/0.58         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.21/0.58  thf('79', plain,
% 0.21/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.58          | (v1_xboole_0 @ X8)
% 0.21/0.58          | ~ (l1_struct_0 @ X9)
% 0.21/0.58          | (v2_struct_0 @ X9)
% 0.21/0.58          | (v1_xboole_0 @ X10)
% 0.21/0.58          | ~ (v2_waybel_0 @ X10 @ (k3_yellow_1 @ X8))
% 0.21/0.58          | ~ (v13_waybel_0 @ X10 @ (k3_yellow_1 @ X8))
% 0.21/0.58          | ~ (m1_subset_1 @ X10 @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X8))))
% 0.21/0.58          | (l1_waybel_0 @ (k3_yellow19 @ X9 @ X8 @ X10) @ X9))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.21/0.58  thf('80', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('81', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('82', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('83', plain,
% 0.21/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.58          | (v1_xboole_0 @ X8)
% 0.21/0.58          | ~ (l1_struct_0 @ X9)
% 0.21/0.58          | (v2_struct_0 @ X9)
% 0.21/0.58          | (v1_xboole_0 @ X10)
% 0.21/0.58          | ~ (v2_waybel_0 @ X10 @ (k3_lattice3 @ (k1_lattice3 @ X8)))
% 0.21/0.58          | ~ (v13_waybel_0 @ X10 @ (k3_lattice3 @ (k1_lattice3 @ X8)))
% 0.21/0.58          | ~ (m1_subset_1 @ X10 @ 
% 0.21/0.58               (k1_zfmisc_1 @ 
% 0.21/0.58                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X8)))))
% 0.21/0.58          | (l1_waybel_0 @ (k3_yellow19 @ X9 @ X8 @ X10) @ X9))),
% 0.21/0.58      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 0.21/0.58  thf('84', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.21/0.58          | ~ (v13_waybel_0 @ sk_B @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58          | ~ (v2_waybel_0 @ sk_B @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['78', '83'])).
% 0.21/0.58  thf('85', plain,
% 0.21/0.58      ((v13_waybel_0 @ sk_B @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.58  thf('86', plain,
% 0.21/0.58      ((v2_waybel_0 @ sk_B @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.58  thf('87', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.21/0.58  thf('88', plain,
% 0.21/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B)
% 0.21/0.58        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.58           sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['77', '87'])).
% 0.21/0.58  thf('89', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.58           sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['76', '88'])).
% 0.21/0.58  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('91', plain,
% 0.21/0.58      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.58         sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['89', '90'])).
% 0.21/0.58  thf('92', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('93', plain,
% 0.21/0.58      (![X2 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('94', plain,
% 0.21/0.58      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.21/0.58        | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('95', plain,
% 0.21/0.58      (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('split', [status(esa)], ['94'])).
% 0.21/0.58  thf('96', plain,
% 0.21/0.58      ((((r3_waybel_9 @ sk_A @ 
% 0.21/0.58          (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.21/0.58         | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['93', '95'])).
% 0.21/0.58  thf('97', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.58         | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C)))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['92', '96'])).
% 0.21/0.58  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('99', plain,
% 0.21/0.58      (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58         (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['97', '98'])).
% 0.21/0.58  thf('100', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t12_yellow19, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.58             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.58           ( ![C:$i]:
% 0.21/0.58             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.58               ( ( r3_waybel_9 @ A @ B @ C ) <=>
% 0.21/0.58                 ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.21/0.58  thf('101', plain,
% 0.21/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.58         ((v2_struct_0 @ X17)
% 0.21/0.58          | ~ (v4_orders_2 @ X17)
% 0.21/0.58          | ~ (v7_waybel_0 @ X17)
% 0.21/0.58          | ~ (l1_waybel_0 @ X17 @ X18)
% 0.21/0.58          | ~ (r3_waybel_9 @ X18 @ X17 @ X19)
% 0.21/0.58          | (r1_waybel_7 @ X18 @ (k2_yellow19 @ X18 @ X17) @ X19)
% 0.21/0.58          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.21/0.58          | ~ (l1_pre_topc @ X18)
% 0.21/0.58          | ~ (v2_pre_topc @ X18)
% 0.21/0.58          | (v2_struct_0 @ X18))),
% 0.21/0.58      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.21/0.58  thf('102', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v2_struct_0 @ sk_A)
% 0.21/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.58          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.21/0.58          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.21/0.58          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.21/0.58          | ~ (v7_waybel_0 @ X0)
% 0.21/0.58          | ~ (v4_orders_2 @ X0)
% 0.21/0.58          | (v2_struct_0 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['100', '101'])).
% 0.21/0.58  thf('103', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('105', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v2_struct_0 @ sk_A)
% 0.21/0.58          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C)
% 0.21/0.58          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C)
% 0.21/0.58          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.21/0.58          | ~ (v7_waybel_0 @ X0)
% 0.21/0.58          | ~ (v4_orders_2 @ X0)
% 0.21/0.58          | (v2_struct_0 @ X0))),
% 0.21/0.58      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.21/0.58  thf('106', plain,
% 0.21/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58         | ~ (l1_waybel_0 @ 
% 0.21/0.58              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.21/0.58            (k2_yellow19 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.21/0.58            sk_C)
% 0.21/0.58         | (v2_struct_0 @ sk_A)))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['99', '105'])).
% 0.21/0.58  thf('107', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.21/0.58            (k2_yellow19 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.21/0.58            sk_C)
% 0.21/0.58         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['91', '106'])).
% 0.21/0.58  thf('108', plain,
% 0.21/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.21/0.58            (k2_yellow19 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.21/0.58            sk_C)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['107'])).
% 0.21/0.58  thf('109', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ 
% 0.21/0.58            (k2_yellow19 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.21/0.58            sk_C)
% 0.21/0.58         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['75', '108'])).
% 0.21/0.58  thf('110', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('111', plain,
% 0.21/0.58      (![X2 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('112', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('113', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.58  thf(t15_yellow19, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.58             ( v1_subset_1 @
% 0.21/0.58               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.58             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.58             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.58             ( m1_subset_1 @
% 0.21/0.58               B @ 
% 0.21/0.58               ( k1_zfmisc_1 @
% 0.21/0.58                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.58           ( ( B ) =
% 0.21/0.58             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.21/0.58  thf('114', plain,
% 0.21/0.58      (![X20 : $i, X21 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ X20)
% 0.21/0.58          | ~ (v1_subset_1 @ X20 @ 
% 0.21/0.58               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X21))))
% 0.21/0.58          | ~ (v2_waybel_0 @ X20 @ (k3_yellow_1 @ (k2_struct_0 @ X21)))
% 0.21/0.58          | ~ (v13_waybel_0 @ X20 @ (k3_yellow_1 @ (k2_struct_0 @ X21)))
% 0.21/0.58          | ~ (m1_subset_1 @ X20 @ 
% 0.21/0.58               (k1_zfmisc_1 @ 
% 0.21/0.58                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X21)))))
% 0.21/0.58          | ((X20)
% 0.21/0.58              = (k2_yellow19 @ X21 @ 
% 0.21/0.58                 (k3_yellow19 @ X21 @ (k2_struct_0 @ X21) @ X20)))
% 0.21/0.58          | ~ (l1_struct_0 @ X21)
% 0.21/0.58          | (v2_struct_0 @ X21))),
% 0.21/0.58      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.21/0.58  thf('115', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('116', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('117', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('118', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('119', plain,
% 0.21/0.58      (![X20 : $i, X21 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ X20)
% 0.21/0.58          | ~ (v1_subset_1 @ X20 @ 
% 0.21/0.58               (u1_struct_0 @ 
% 0.21/0.58                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X21)))))
% 0.21/0.58          | ~ (v2_waybel_0 @ X20 @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X21))))
% 0.21/0.58          | ~ (v13_waybel_0 @ X20 @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X21))))
% 0.21/0.58          | ~ (m1_subset_1 @ X20 @ 
% 0.21/0.58               (k1_zfmisc_1 @ 
% 0.21/0.58                (u1_struct_0 @ 
% 0.21/0.58                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X21))))))
% 0.21/0.58          | ((X20)
% 0.21/0.58              = (k2_yellow19 @ X21 @ 
% 0.21/0.58                 (k3_yellow19 @ X21 @ (k2_struct_0 @ X21) @ X20)))
% 0.21/0.58          | ~ (l1_struct_0 @ X21)
% 0.21/0.58          | (v2_struct_0 @ X21))),
% 0.21/0.58      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 0.21/0.58  thf('120', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_A)
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58        | ((sk_B)
% 0.21/0.58            = (k2_yellow19 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.21/0.58        | ~ (v13_waybel_0 @ sk_B @ 
% 0.21/0.58             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58        | ~ (v2_waybel_0 @ sk_B @ 
% 0.21/0.58             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58        | ~ (v1_subset_1 @ sk_B @ 
% 0.21/0.58             (u1_struct_0 @ 
% 0.21/0.58              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.21/0.58        | (v1_xboole_0 @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['113', '119'])).
% 0.21/0.58  thf('121', plain,
% 0.21/0.58      ((v13_waybel_0 @ sk_B @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.58  thf('122', plain,
% 0.21/0.58      ((v2_waybel_0 @ sk_B @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.58  thf('123', plain,
% 0.21/0.58      ((v1_subset_1 @ sk_B @ 
% 0.21/0.58        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.58      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.58  thf('124', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_A)
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58        | ((sk_B)
% 0.21/0.58            = (k2_yellow19 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.21/0.58        | (v1_xboole_0 @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['120', '121', '122', '123'])).
% 0.21/0.58  thf('125', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B)
% 0.21/0.58        | ((sk_B)
% 0.21/0.58            = (k2_yellow19 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.21/0.58        | (v2_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['112', '124'])).
% 0.21/0.58  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('127', plain,
% 0.21/0.58      (((v1_xboole_0 @ sk_B)
% 0.21/0.58        | ((sk_B)
% 0.21/0.58            = (k2_yellow19 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.21/0.58        | (v2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['125', '126'])).
% 0.21/0.58  thf('128', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('129', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_A)
% 0.21/0.58        | ((sk_B)
% 0.21/0.58            = (k2_yellow19 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.58      inference('clc', [status(thm)], ['127', '128'])).
% 0.21/0.58  thf('130', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('131', plain,
% 0.21/0.58      (((sk_B)
% 0.21/0.58         = (k2_yellow19 @ sk_A @ 
% 0.21/0.58            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.58      inference('clc', [status(thm)], ['129', '130'])).
% 0.21/0.58  thf('132', plain,
% 0.21/0.58      ((((sk_B)
% 0.21/0.58          = (k2_yellow19 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup+', [status(thm)], ['111', '131'])).
% 0.21/0.58  thf('133', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | ((sk_B)
% 0.21/0.58            = (k2_yellow19 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['110', '132'])).
% 0.21/0.58  thf('134', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('135', plain,
% 0.21/0.58      (((sk_B)
% 0.21/0.58         = (k2_yellow19 @ sk_A @ 
% 0.21/0.58            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.58      inference('demod', [status(thm)], ['133', '134'])).
% 0.21/0.58  thf('136', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.21/0.58         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['109', '135'])).
% 0.21/0.58  thf('137', plain,
% 0.21/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['136'])).
% 0.21/0.58  thf('138', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.21/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['59', '137'])).
% 0.21/0.58  thf('139', plain,
% 0.21/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['138'])).
% 0.21/0.58  thf('140', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.58      inference('demod', [status(thm)], ['5', '10'])).
% 0.21/0.58  thf('141', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.21/0.58      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.58  thf('142', plain,
% 0.21/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.58          | (v1_xboole_0 @ X8)
% 0.21/0.58          | ~ (l1_struct_0 @ X9)
% 0.21/0.58          | (v2_struct_0 @ X9)
% 0.21/0.58          | (v1_xboole_0 @ X10)
% 0.21/0.58          | ~ (v2_waybel_0 @ X10 @ (k3_yellow_1 @ X8))
% 0.21/0.58          | ~ (v13_waybel_0 @ X10 @ (k3_yellow_1 @ X8))
% 0.21/0.58          | ~ (m1_subset_1 @ X10 @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X8))))
% 0.21/0.58          | ~ (v2_struct_0 @ (k3_yellow19 @ X9 @ X8 @ X10)))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.21/0.58  thf('143', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('144', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('145', plain,
% 0.21/0.58      (![X5 : $i]: ((k3_yellow_1 @ X5) = (k3_lattice3 @ (k1_lattice3 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.58  thf('146', plain,
% 0.21/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.58          | (v1_xboole_0 @ X8)
% 0.21/0.58          | ~ (l1_struct_0 @ X9)
% 0.21/0.58          | (v2_struct_0 @ X9)
% 0.21/0.58          | (v1_xboole_0 @ X10)
% 0.21/0.58          | ~ (v2_waybel_0 @ X10 @ (k3_lattice3 @ (k1_lattice3 @ X8)))
% 0.21/0.58          | ~ (v13_waybel_0 @ X10 @ (k3_lattice3 @ (k1_lattice3 @ X8)))
% 0.21/0.58          | ~ (m1_subset_1 @ X10 @ 
% 0.21/0.58               (k1_zfmisc_1 @ 
% 0.21/0.58                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X8)))))
% 0.21/0.58          | ~ (v2_struct_0 @ (k3_yellow19 @ X9 @ X8 @ X10)))),
% 0.21/0.58      inference('demod', [status(thm)], ['142', '143', '144', '145'])).
% 0.21/0.58  thf('147', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | ~ (v13_waybel_0 @ sk_B @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58          | ~ (v2_waybel_0 @ sk_B @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['141', '146'])).
% 0.21/0.58  thf('148', plain,
% 0.21/0.58      ((v13_waybel_0 @ sk_B @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.58  thf('149', plain,
% 0.21/0.58      ((v2_waybel_0 @ sk_B @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.58  thf('150', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['147', '148', '149'])).
% 0.21/0.58  thf('151', plain,
% 0.21/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B)
% 0.21/0.58        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['140', '150'])).
% 0.21/0.58  thf('152', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['139', '151'])).
% 0.21/0.58  thf('153', plain,
% 0.21/0.58      (((~ (l1_struct_0 @ sk_A)
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['152'])).
% 0.21/0.58  thf('154', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['3', '153'])).
% 0.21/0.58  thf('155', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('156', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.21/0.58         <= (((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['154', '155'])).
% 0.21/0.58  thf('157', plain,
% 0.21/0.58      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.21/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('158', plain,
% 0.21/0.58      ((((v1_xboole_0 @ sk_B)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['156', '157'])).
% 0.21/0.58  thf('159', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('160', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.21/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('clc', [status(thm)], ['158', '159'])).
% 0.21/0.58  thf('161', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('162', plain,
% 0.21/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.21/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('clc', [status(thm)], ['160', '161'])).
% 0.21/0.58  thf(fc2_struct_0, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.58       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.58  thf('163', plain,
% 0.21/0.58      (![X4 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ (u1_struct_0 @ X4))
% 0.21/0.58          | ~ (l1_struct_0 @ X4)
% 0.21/0.58          | (v2_struct_0 @ X4))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.58  thf('164', plain,
% 0.21/0.58      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['162', '163'])).
% 0.21/0.58  thf('165', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('166', plain,
% 0.21/0.58      ((~ (l1_struct_0 @ sk_A))
% 0.21/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('clc', [status(thm)], ['164', '165'])).
% 0.21/0.58  thf('167', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A))
% 0.21/0.58         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['2', '166'])).
% 0.21/0.58  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('169', plain,
% 0.21/0.58      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.21/0.58       ~
% 0.21/0.58       ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['167', '168'])).
% 0.21/0.58  thf('170', plain,
% 0.21/0.58      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.21/0.58       ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.21/0.58      inference('split', [status(esa)], ['94'])).
% 0.21/0.58  thf('171', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('172', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('173', plain,
% 0.21/0.58      (![X2 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('174', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('175', plain,
% 0.21/0.58      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.21/0.58         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.58      inference('split', [status(esa)], ['94'])).
% 0.21/0.58  thf('176', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('177', plain,
% 0.21/0.58      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58        | (v1_xboole_0 @ sk_B)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.58  thf('178', plain,
% 0.21/0.58      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58        | (v1_xboole_0 @ sk_B)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.58  thf('179', plain,
% 0.21/0.58      (![X2 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('180', plain,
% 0.21/0.58      (![X2 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('181', plain,
% 0.21/0.58      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.58         sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['89', '90'])).
% 0.21/0.58  thf('182', plain,
% 0.21/0.58      (![X2 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('183', plain,
% 0.21/0.58      (((sk_B)
% 0.21/0.58         = (k2_yellow19 @ sk_A @ 
% 0.21/0.58            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.58      inference('clc', [status(thm)], ['129', '130'])).
% 0.21/0.58  thf('184', plain,
% 0.21/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.58         ((v2_struct_0 @ X17)
% 0.21/0.58          | ~ (v4_orders_2 @ X17)
% 0.21/0.58          | ~ (v7_waybel_0 @ X17)
% 0.21/0.58          | ~ (l1_waybel_0 @ X17 @ X18)
% 0.21/0.58          | ~ (r1_waybel_7 @ X18 @ (k2_yellow19 @ X18 @ X17) @ X19)
% 0.21/0.58          | (r3_waybel_9 @ X18 @ X17 @ X19)
% 0.21/0.58          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.21/0.58          | ~ (l1_pre_topc @ X18)
% 0.21/0.58          | ~ (v2_pre_topc @ X18)
% 0.21/0.58          | (v2_struct_0 @ X18))),
% 0.21/0.58      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.21/0.58  thf('185', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.21/0.58          | ~ (l1_waybel_0 @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.21/0.58          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['183', '184'])).
% 0.21/0.58  thf('186', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('187', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('188', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.21/0.58          | ~ (l1_waybel_0 @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.21/0.58          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.58      inference('demod', [status(thm)], ['185', '186', '187'])).
% 0.21/0.58  thf('189', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (l1_waybel_0 @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.21/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['182', '188'])).
% 0.21/0.58  thf('190', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.21/0.58          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['181', '189'])).
% 0.21/0.58  thf('191', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (l1_struct_0 @ sk_A)
% 0.21/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['190'])).
% 0.21/0.58  thf('192', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.21/0.58          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['180', '191'])).
% 0.21/0.58  thf('193', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['192'])).
% 0.21/0.58  thf('194', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.21/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['179', '193'])).
% 0.21/0.58  thf('195', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['194'])).
% 0.21/0.58  thf('196', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.21/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['178', '195'])).
% 0.21/0.58  thf('197', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['196'])).
% 0.21/0.58  thf('198', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.21/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['177', '197'])).
% 0.21/0.58  thf('199', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['198'])).
% 0.21/0.58  thf('200', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (l1_pre_topc @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.21/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['176', '199'])).
% 0.21/0.58  thf('201', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('202', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (v2_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.21/0.58          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.58      inference('demod', [status(thm)], ['200', '201'])).
% 0.21/0.58  thf('203', plain,
% 0.21/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58         | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.21/0.58         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['175', '202'])).
% 0.21/0.58  thf('204', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('205', plain,
% 0.21/0.58      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58         | (r3_waybel_9 @ sk_A @ 
% 0.21/0.58            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['203', '204'])).
% 0.21/0.58  thf('206', plain,
% 0.21/0.58      ((~ (r3_waybel_9 @ sk_A @ 
% 0.21/0.58           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('207', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['205', '206'])).
% 0.21/0.58  thf('208', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.58      inference('demod', [status(thm)], ['5', '10'])).
% 0.21/0.58  thf('209', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('210', plain,
% 0.21/0.58      (![X2 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('211', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.58  thf('212', plain,
% 0.21/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.58          | (v1_xboole_0 @ X8)
% 0.21/0.58          | ~ (l1_struct_0 @ X9)
% 0.21/0.58          | (v2_struct_0 @ X9)
% 0.21/0.58          | (v1_xboole_0 @ X10)
% 0.21/0.58          | ~ (v2_waybel_0 @ X10 @ (k3_lattice3 @ (k1_lattice3 @ X8)))
% 0.21/0.58          | ~ (v13_waybel_0 @ X10 @ (k3_lattice3 @ (k1_lattice3 @ X8)))
% 0.21/0.58          | ~ (m1_subset_1 @ X10 @ 
% 0.21/0.58               (k1_zfmisc_1 @ 
% 0.21/0.58                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X8)))))
% 0.21/0.58          | ~ (v2_struct_0 @ (k3_yellow19 @ X9 @ X8 @ X10)))),
% 0.21/0.58      inference('demod', [status(thm)], ['142', '143', '144', '145'])).
% 0.21/0.58  thf('213', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | ~ (v13_waybel_0 @ sk_B @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58          | ~ (v2_waybel_0 @ sk_B @ 
% 0.21/0.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['211', '212'])).
% 0.21/0.58  thf('214', plain,
% 0.21/0.58      ((v13_waybel_0 @ sk_B @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.58  thf('215', plain,
% 0.21/0.58      ((v2_waybel_0 @ sk_B @ 
% 0.21/0.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.58  thf('216', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['213', '214', '215'])).
% 0.21/0.58  thf('217', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['210', '216'])).
% 0.21/0.58  thf('218', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (l1_pre_topc @ sk_A)
% 0.21/0.58          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['209', '217'])).
% 0.21/0.58  thf('219', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('220', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.58          | (v1_xboole_0 @ sk_B)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['218', '219'])).
% 0.21/0.58  thf('221', plain,
% 0.21/0.58      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | (v1_xboole_0 @ sk_B)
% 0.21/0.58        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['208', '220'])).
% 0.21/0.58  thf('222', plain,
% 0.21/0.58      ((((v1_xboole_0 @ sk_B)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['207', '221'])).
% 0.21/0.58  thf('223', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.58         | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['222'])).
% 0.21/0.58  thf('224', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['174', '223'])).
% 0.21/0.58  thf('225', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('226', plain,
% 0.21/0.58      ((((v1_xboole_0 @ sk_B)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['224', '225'])).
% 0.21/0.58  thf('227', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['173', '226'])).
% 0.21/0.58  thf('228', plain,
% 0.21/0.58      ((((v1_xboole_0 @ sk_B)
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['227'])).
% 0.21/0.58  thf('229', plain,
% 0.21/0.58      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['172', '228'])).
% 0.21/0.58  thf('230', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('231', plain,
% 0.21/0.58      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58         | (v2_struct_0 @ sk_A)
% 0.21/0.58         | (v1_xboole_0 @ sk_B)))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['229', '230'])).
% 0.21/0.58  thf('232', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('233', plain,
% 0.21/0.58      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.58      inference('clc', [status(thm)], ['231', '232'])).
% 0.21/0.58  thf('234', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('235', plain,
% 0.21/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.58      inference('clc', [status(thm)], ['233', '234'])).
% 0.21/0.58  thf('236', plain,
% 0.21/0.58      (![X4 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ (u1_struct_0 @ X4))
% 0.21/0.58          | ~ (l1_struct_0 @ X4)
% 0.21/0.58          | (v2_struct_0 @ X4))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.58  thf('237', plain,
% 0.21/0.58      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['235', '236'])).
% 0.21/0.58  thf('238', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('239', plain,
% 0.21/0.58      ((~ (l1_struct_0 @ sk_A))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.58      inference('clc', [status(thm)], ['237', '238'])).
% 0.21/0.58  thf('240', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C)) & 
% 0.21/0.58             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['171', '239'])).
% 0.21/0.58  thf('241', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('242', plain,
% 0.21/0.58      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.21/0.58       ((r3_waybel_9 @ sk_A @ 
% 0.21/0.58         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['240', '241'])).
% 0.21/0.58  thf('243', plain, ($false),
% 0.21/0.58      inference('sat_resolution*', [status(thm)], ['1', '169', '170', '242'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.21/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
