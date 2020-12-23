%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oXIU1gJ9sM

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:53 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  291 ( 940 expanded)
%              Number of leaves         :   44 ( 308 expanded)
%              Depth                    :   40
%              Number of atoms          : 3855 (17471 expanded)
%              Number of equality atoms :   49 ( 233 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( r2_hidden @ X9 @ ( k1_connsp_2 @ X10 @ X9 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_C @ ( k1_connsp_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( k1_connsp_2 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ sk_C @ ( k1_connsp_2 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('10',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('11',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('14',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('16',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('18',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

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

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_xboole_0 @ X15 )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( v2_waybel_0 @ X17 @ ( k3_yellow_1 @ X15 ) )
      | ~ ( v13_waybel_0 @ X17 @ ( k3_yellow_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X15 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X16 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('25',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('26',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('27',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('28',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_xboole_0 @ X15 )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( v2_waybel_0 @ X17 @ ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) )
      | ~ ( v13_waybel_0 @ X17 @ ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X15 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X16 @ X15 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('31',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('32',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('34',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('40',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('43',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['29','38','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','48'])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

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

thf('56',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_xboole_0 @ X18 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( v1_subset_1 @ X20 @ ( u1_struct_0 @ ( k3_yellow_1 @ X18 ) ) )
      | ~ ( v2_waybel_0 @ X20 @ ( k3_yellow_1 @ X18 ) )
      | ~ ( v13_waybel_0 @ X20 @ ( k3_yellow_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X18 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X19 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('57',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('58',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('59',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('60',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('61',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v1_xboole_0 @ X18 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( v1_subset_1 @ X20 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) ) )
      | ~ ( v2_waybel_0 @ X20 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) )
      | ~ ( v13_waybel_0 @ X20 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X19 @ X18 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['56','57','58','59','60'])).

thf('62',plain,(
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
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('64',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('65',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('66',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('69',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','73'])).

thf('75',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','74'])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('80',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

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

thf('82',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v2_waybel_0 @ X14 @ ( k3_yellow_1 @ X12 ) )
      | ~ ( v13_waybel_0 @ X14 @ ( k3_yellow_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X12 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X13 @ X12 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('83',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('84',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('85',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('86',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v2_waybel_0 @ X14 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) )
      | ~ ( v13_waybel_0 @ X14 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X13 @ X12 @ X14 ) @ X13 ) ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('89',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['80','90'])).

thf('92',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('96',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('97',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['97'])).

thf('99',plain,
    ( ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['96','98'])).

thf('100',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['95','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

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

thf('103',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( l1_waybel_0 @ X21 @ X22 )
      | ~ ( r2_hidden @ X23 @ ( k10_yellow_6 @ X22 @ X21 ) )
      | ( r2_waybel_7 @ X22 @ ( k2_yellow19 @ X22 @ X21 ) @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow19])).

thf('104',plain,
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
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('109',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('110',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('111',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

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
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v1_subset_1 @ X24 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X25 ) ) ) )
      | ~ ( v2_waybel_0 @ X24 @ ( k3_yellow_1 @ ( k2_struct_0 @ X25 ) ) )
      | ~ ( v13_waybel_0 @ X24 @ ( k3_yellow_1 @ ( k2_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X25 ) ) ) ) )
      | ( X24
        = ( k2_yellow19 @ X25 @ ( k3_yellow19 @ X25 @ ( k2_struct_0 @ X25 ) @ X24 ) ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('113',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('114',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('115',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('116',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('117',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v1_subset_1 @ X24 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X25 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X24 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X25 ) ) ) )
      | ~ ( v13_waybel_0 @ X24 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X25 ) ) ) ) ) )
      | ( X24
        = ( k2_yellow19 @ X25 @ ( k3_yellow19 @ X25 @ ( k2_struct_0 @ X25 ) @ X24 ) ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
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
    inference(demod,[status(thm)],['32','33'])).

thf('120',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('121',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

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
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['104','105','106','107','133'])).

thf('135',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['94','134'])).

thf('136',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
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
    inference('sup-',[status(thm)],['78','136'])).

thf('138',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','138'])).

thf('140',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('142',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('143',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v2_waybel_0 @ X14 @ ( k3_yellow_1 @ X12 ) )
      | ~ ( v13_waybel_0 @ X14 @ ( k3_yellow_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X12 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X13 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('144',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('145',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('146',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_1 @ X11 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('147',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v2_waybel_0 @ X14 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) )
      | ~ ( v13_waybel_0 @ X14 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X13 @ X12 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['143','144','145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['142','147'])).

thf('149',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('150',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['141','151'])).

thf('153',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['140','152'])).

thf('154',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','154'])).

thf('156',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('159',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('165',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('166',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['169','170'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('172',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_A @ sk_C ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['163','173'])).

thf('175',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','174'])).

thf('176',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['97'])).

thf('177',plain,(
    r2_hidden @ sk_C @ ( k1_connsp_2 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('178',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('179',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('180',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('181',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['97'])).

thf('182',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('183',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('184',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('185',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('186',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('187',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('188',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('189',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('190',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( l1_waybel_0 @ X21 @ X22 )
      | ~ ( r2_waybel_7 @ X22 @ ( k2_yellow19 @ X22 @ X21 ) @ X23 )
      | ( r2_hidden @ X23 @ ( k10_yellow_6 @ X22 @ X21 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow19])).

thf('191',plain,(
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
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['191','192','193'])).

thf('195',plain,(
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
    inference('sup-',[status(thm)],['188','194'])).

thf('196',plain,(
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
    inference('sup-',[status(thm)],['187','195'])).

thf('197',plain,(
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
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,(
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
    inference('sup-',[status(thm)],['186','197'])).

thf('199',plain,(
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
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,(
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
    inference('sup-',[status(thm)],['185','199'])).

thf('201',plain,(
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
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,(
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
    inference('sup-',[status(thm)],['184','201'])).

thf('203',plain,(
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
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,(
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
    inference('sup-',[status(thm)],['183','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['182','205'])).

thf('207',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['181','208'])).

thf('210',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['209','210'])).

thf('212',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('213',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('215',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('216',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('217',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('218',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v2_waybel_0 @ X14 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) )
      | ~ ( v13_waybel_0 @ X14 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X12 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X13 @ X12 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['143','144','145','146'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('221',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['216','222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['215','223'])).

thf('225',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['224','225'])).

thf('227',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['214','226'])).

thf('228',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['213','227'])).

thf('229',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['180','229'])).

thf('231',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['179','232'])).

thf('234',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['233'])).

thf('235',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['178','234'])).

thf('236',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('240',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['239','240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('243',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_A @ sk_C ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['177','243'])).

thf('245',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','175','176','244'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oXIU1gJ9sM
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:57:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.57  % Solved by: fo/fo7.sh
% 0.40/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.57  % done 189 iterations in 0.103s
% 0.40/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.57  % SZS output start Refutation
% 0.40/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.40/0.57  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.40/0.57  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.40/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.40/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.57  thf(r2_waybel_7_type, type, r2_waybel_7: $i > $i > $i > $o).
% 0.40/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.57  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.40/0.57  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.40/0.57  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.40/0.57  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.40/0.57  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.40/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.57  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.40/0.57  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.40/0.57  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.40/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.57  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.40/0.57  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.40/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.57  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.40/0.57  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.40/0.57  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.40/0.57  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.40/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.57  thf(t18_yellow19, conjecture,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.57       ( ![B:$i]:
% 0.40/0.57         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.57             ( v1_subset_1 @
% 0.40/0.57               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.57             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.57             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.57             ( m1_subset_1 @
% 0.40/0.57               B @ 
% 0.40/0.57               ( k1_zfmisc_1 @
% 0.40/0.57                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.57           ( ![C:$i]:
% 0.40/0.57             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.57               ( ( r2_hidden @
% 0.40/0.57                   C @ 
% 0.40/0.57                   ( k10_yellow_6 @
% 0.40/0.57                     A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) <=>
% 0.40/0.57                 ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.40/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.57    (~( ![A:$i]:
% 0.40/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.40/0.57            ( l1_pre_topc @ A ) ) =>
% 0.40/0.57          ( ![B:$i]:
% 0.40/0.57            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.57                ( v1_subset_1 @
% 0.40/0.57                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.57                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.57                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.57                ( m1_subset_1 @
% 0.40/0.57                  B @ 
% 0.40/0.57                  ( k1_zfmisc_1 @
% 0.40/0.57                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.57              ( ![C:$i]:
% 0.40/0.57                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.57                  ( ( r2_hidden @
% 0.40/0.57                      C @ 
% 0.40/0.57                      ( k10_yellow_6 @
% 0.40/0.57                        A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) <=>
% 0.40/0.57                    ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.40/0.57    inference('cnf.neg', [status(esa)], [t18_yellow19])).
% 0.40/0.57  thf('0', plain,
% 0.40/0.57      ((~ (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.57        | ~ (r2_hidden @ sk_C @ 
% 0.40/0.57             (k10_yellow_6 @ sk_A @ 
% 0.40/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('1', plain,
% 0.40/0.57      (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.40/0.57       ~
% 0.40/0.57       ((r2_hidden @ sk_C @ 
% 0.40/0.57         (k10_yellow_6 @ sk_A @ 
% 0.40/0.57          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.40/0.57      inference('split', [status(esa)], ['0'])).
% 0.40/0.57  thf('2', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(t30_connsp_2, axiom,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.57       ( ![B:$i]:
% 0.40/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.57           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.40/0.57  thf('3', plain,
% 0.40/0.57      (![X9 : $i, X10 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.40/0.57          | (r2_hidden @ X9 @ (k1_connsp_2 @ X10 @ X9))
% 0.40/0.57          | ~ (l1_pre_topc @ X10)
% 0.40/0.57          | ~ (v2_pre_topc @ X10)
% 0.40/0.57          | (v2_struct_0 @ X10))),
% 0.40/0.57      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.40/0.57  thf('4', plain,
% 0.40/0.57      (((v2_struct_0 @ sk_A)
% 0.40/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.40/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.40/0.57        | (r2_hidden @ sk_C @ (k1_connsp_2 @ sk_A @ sk_C)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.57  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('7', plain,
% 0.40/0.57      (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_C @ (k1_connsp_2 @ sk_A @ sk_C)))),
% 0.40/0.57      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.40/0.57  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('9', plain, ((r2_hidden @ sk_C @ (k1_connsp_2 @ sk_A @ sk_C))),
% 0.40/0.57      inference('clc', [status(thm)], ['7', '8'])).
% 0.40/0.57  thf(dt_l1_pre_topc, axiom,
% 0.40/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.40/0.57  thf('10', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.57  thf('11', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.57  thf(dt_k2_subset_1, axiom,
% 0.40/0.57    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.40/0.57  thf('12', plain,
% 0.40/0.57      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.40/0.57  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.40/0.57  thf('13', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.40/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.40/0.57  thf('14', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.40/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.40/0.57  thf('15', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.57  thf(d3_struct_0, axiom,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.40/0.57  thf('16', plain,
% 0.40/0.57      (![X5 : $i]:
% 0.40/0.57         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.57  thf('17', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_B @ 
% 0.40/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(d2_yellow_1, axiom,
% 0.40/0.57    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.40/0.57  thf('18', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('19', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_B @ 
% 0.40/0.57        (k1_zfmisc_1 @ 
% 0.40/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.40/0.57  thf('20', plain,
% 0.40/0.57      (((m1_subset_1 @ sk_B @ 
% 0.40/0.57         (k1_zfmisc_1 @ 
% 0.40/0.57          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 0.40/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.57      inference('sup+', [status(thm)], ['16', '19'])).
% 0.40/0.57  thf('21', plain,
% 0.40/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.57        | (m1_subset_1 @ sk_B @ 
% 0.40/0.57           (k1_zfmisc_1 @ 
% 0.40/0.57            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['15', '20'])).
% 0.40/0.57  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('23', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_B @ 
% 0.40/0.57        (k1_zfmisc_1 @ 
% 0.40/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.40/0.57      inference('demod', [status(thm)], ['21', '22'])).
% 0.40/0.57  thf(fc4_yellow19, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.40/0.57         ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.40/0.57         ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.57         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.57         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.57         ( m1_subset_1 @
% 0.40/0.57           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.40/0.57       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.40/0.57         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.40/0.57         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.40/0.57         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.40/0.57  thf('24', plain,
% 0.40/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.40/0.57          | (v1_xboole_0 @ X15)
% 0.40/0.57          | ~ (l1_struct_0 @ X16)
% 0.40/0.57          | (v2_struct_0 @ X16)
% 0.40/0.57          | (v1_xboole_0 @ X17)
% 0.40/0.57          | ~ (v2_waybel_0 @ X17 @ (k3_yellow_1 @ X15))
% 0.40/0.57          | ~ (v13_waybel_0 @ X17 @ (k3_yellow_1 @ X15))
% 0.40/0.57          | ~ (m1_subset_1 @ X17 @ 
% 0.40/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X15))))
% 0.40/0.57          | (v4_orders_2 @ (k3_yellow19 @ X16 @ X15 @ X17)))),
% 0.40/0.57      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.40/0.57  thf('25', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('26', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('27', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('28', plain,
% 0.40/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.40/0.57          | (v1_xboole_0 @ X15)
% 0.40/0.57          | ~ (l1_struct_0 @ X16)
% 0.40/0.57          | (v2_struct_0 @ X16)
% 0.40/0.57          | (v1_xboole_0 @ X17)
% 0.40/0.57          | ~ (v2_waybel_0 @ X17 @ (k3_lattice3 @ (k1_lattice3 @ X15)))
% 0.40/0.57          | ~ (v13_waybel_0 @ X17 @ (k3_lattice3 @ (k1_lattice3 @ X15)))
% 0.40/0.57          | ~ (m1_subset_1 @ X17 @ 
% 0.40/0.57               (k1_zfmisc_1 @ 
% 0.40/0.57                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X15)))))
% 0.40/0.57          | (v4_orders_2 @ (k3_yellow19 @ X16 @ X15 @ X17)))),
% 0.40/0.57      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.40/0.57  thf('29', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | (v2_struct_0 @ X0)
% 0.40/0.57          | ~ (l1_struct_0 @ X0)
% 0.40/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['23', '28'])).
% 0.40/0.57  thf('30', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.57  thf('31', plain,
% 0.40/0.57      (![X5 : $i]:
% 0.40/0.57         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.57  thf('32', plain,
% 0.40/0.57      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('33', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('34', plain,
% 0.40/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.40/0.57  thf('35', plain,
% 0.40/0.57      (((v13_waybel_0 @ sk_B @ 
% 0.40/0.57         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.57      inference('sup+', [status(thm)], ['31', '34'])).
% 0.40/0.57  thf('36', plain,
% 0.40/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.57        | (v13_waybel_0 @ sk_B @ 
% 0.40/0.57           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['30', '35'])).
% 0.40/0.57  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('38', plain,
% 0.40/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.57      inference('demod', [status(thm)], ['36', '37'])).
% 0.40/0.57  thf('39', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.57  thf('40', plain,
% 0.40/0.57      (![X5 : $i]:
% 0.40/0.57         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.57  thf('41', plain,
% 0.40/0.57      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('42', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('43', plain,
% 0.40/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.57      inference('demod', [status(thm)], ['41', '42'])).
% 0.40/0.57  thf('44', plain,
% 0.40/0.57      (((v2_waybel_0 @ sk_B @ 
% 0.40/0.57         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.57      inference('sup+', [status(thm)], ['40', '43'])).
% 0.40/0.57  thf('45', plain,
% 0.40/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.57        | (v2_waybel_0 @ sk_B @ 
% 0.40/0.57           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['39', '44'])).
% 0.40/0.57  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('47', plain,
% 0.40/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.57      inference('demod', [status(thm)], ['45', '46'])).
% 0.40/0.57  thf('48', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | (v2_struct_0 @ X0)
% 0.40/0.57          | ~ (l1_struct_0 @ X0)
% 0.40/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.57      inference('demod', [status(thm)], ['29', '38', '47'])).
% 0.40/0.57  thf('49', plain,
% 0.40/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57        | (v2_struct_0 @ sk_A)
% 0.40/0.57        | (v1_xboole_0 @ sk_B)
% 0.40/0.57        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['14', '48'])).
% 0.40/0.57  thf('50', plain,
% 0.40/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.57        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57        | (v1_xboole_0 @ sk_B)
% 0.40/0.57        | (v2_struct_0 @ sk_A)
% 0.40/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['11', '49'])).
% 0.40/0.57  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('52', plain,
% 0.40/0.57      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57        | (v1_xboole_0 @ sk_B)
% 0.40/0.57        | (v2_struct_0 @ sk_A)
% 0.40/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('demod', [status(thm)], ['50', '51'])).
% 0.40/0.57  thf('53', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.57  thf('54', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.40/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.40/0.57  thf('55', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_B @ 
% 0.40/0.57        (k1_zfmisc_1 @ 
% 0.40/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.40/0.57      inference('demod', [status(thm)], ['21', '22'])).
% 0.40/0.57  thf(fc5_yellow19, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.40/0.57         ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.40/0.57         ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.57         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.40/0.57         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.57         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.57         ( m1_subset_1 @
% 0.40/0.57           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.40/0.57       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.40/0.57         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.40/0.57         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.40/0.57  thf('56', plain,
% 0.40/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.40/0.57          | (v1_xboole_0 @ X18)
% 0.40/0.57          | ~ (l1_struct_0 @ X19)
% 0.40/0.57          | (v2_struct_0 @ X19)
% 0.40/0.57          | (v1_xboole_0 @ X20)
% 0.40/0.57          | ~ (v1_subset_1 @ X20 @ (u1_struct_0 @ (k3_yellow_1 @ X18)))
% 0.40/0.57          | ~ (v2_waybel_0 @ X20 @ (k3_yellow_1 @ X18))
% 0.40/0.57          | ~ (v13_waybel_0 @ X20 @ (k3_yellow_1 @ X18))
% 0.40/0.57          | ~ (m1_subset_1 @ X20 @ 
% 0.40/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X18))))
% 0.40/0.57          | (v7_waybel_0 @ (k3_yellow19 @ X19 @ X18 @ X20)))),
% 0.40/0.57      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.40/0.57  thf('57', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('58', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('59', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('60', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('61', plain,
% 0.40/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.40/0.57          | (v1_xboole_0 @ X18)
% 0.40/0.57          | ~ (l1_struct_0 @ X19)
% 0.40/0.57          | (v2_struct_0 @ X19)
% 0.40/0.57          | (v1_xboole_0 @ X20)
% 0.40/0.57          | ~ (v1_subset_1 @ X20 @ 
% 0.40/0.57               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18))))
% 0.40/0.57          | ~ (v2_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.40/0.57          | ~ (v13_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.40/0.57          | ~ (m1_subset_1 @ X20 @ 
% 0.40/0.57               (k1_zfmisc_1 @ 
% 0.40/0.57                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18)))))
% 0.40/0.57          | (v7_waybel_0 @ (k3_yellow19 @ X19 @ X18 @ X20)))),
% 0.40/0.57      inference('demod', [status(thm)], ['56', '57', '58', '59', '60'])).
% 0.40/0.57  thf('62', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57          | ~ (v1_subset_1 @ sk_B @ 
% 0.40/0.57               (u1_struct_0 @ 
% 0.40/0.57                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | (v2_struct_0 @ X0)
% 0.40/0.57          | ~ (l1_struct_0 @ X0)
% 0.40/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['55', '61'])).
% 0.40/0.57  thf('63', plain,
% 0.40/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.57      inference('demod', [status(thm)], ['36', '37'])).
% 0.40/0.57  thf('64', plain,
% 0.40/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.57      inference('demod', [status(thm)], ['45', '46'])).
% 0.40/0.57  thf('65', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.57  thf('66', plain,
% 0.40/0.57      (![X5 : $i]:
% 0.40/0.57         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.57  thf('67', plain,
% 0.40/0.57      ((v1_subset_1 @ sk_B @ 
% 0.40/0.57        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('68', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('69', plain,
% 0.40/0.57      ((v1_subset_1 @ sk_B @ 
% 0.40/0.57        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.57      inference('demod', [status(thm)], ['67', '68'])).
% 0.40/0.57  thf('70', plain,
% 0.40/0.57      (((v1_subset_1 @ sk_B @ 
% 0.40/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.40/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.57      inference('sup+', [status(thm)], ['66', '69'])).
% 0.40/0.57  thf('71', plain,
% 0.40/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.57        | (v1_subset_1 @ sk_B @ 
% 0.40/0.57           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['65', '70'])).
% 0.40/0.57  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('73', plain,
% 0.40/0.57      ((v1_subset_1 @ sk_B @ 
% 0.40/0.57        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.57      inference('demod', [status(thm)], ['71', '72'])).
% 0.40/0.57  thf('74', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | (v2_struct_0 @ X0)
% 0.40/0.57          | ~ (l1_struct_0 @ X0)
% 0.40/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.57      inference('demod', [status(thm)], ['62', '63', '64', '73'])).
% 0.40/0.57  thf('75', plain,
% 0.40/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57        | (v2_struct_0 @ sk_A)
% 0.40/0.57        | (v1_xboole_0 @ sk_B)
% 0.40/0.57        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['54', '74'])).
% 0.40/0.57  thf('76', plain,
% 0.40/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.57        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57        | (v1_xboole_0 @ sk_B)
% 0.40/0.57        | (v2_struct_0 @ sk_A)
% 0.40/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['53', '75'])).
% 0.40/0.57  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('78', plain,
% 0.40/0.57      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57        | (v1_xboole_0 @ sk_B)
% 0.40/0.57        | (v2_struct_0 @ sk_A)
% 0.40/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('demod', [status(thm)], ['76', '77'])).
% 0.40/0.57  thf('79', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.57  thf('80', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.40/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.40/0.57  thf('81', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_B @ 
% 0.40/0.57        (k1_zfmisc_1 @ 
% 0.40/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.40/0.57      inference('demod', [status(thm)], ['21', '22'])).
% 0.40/0.57  thf(dt_k3_yellow19, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.40/0.57         ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.40/0.57         ( ~( v1_xboole_0 @ C ) ) & 
% 0.40/0.57         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.57         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.40/0.57         ( m1_subset_1 @
% 0.40/0.57           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.40/0.57       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.40/0.57         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.40/0.57         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.40/0.57  thf('82', plain,
% 0.40/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.40/0.57          | (v1_xboole_0 @ X12)
% 0.40/0.57          | ~ (l1_struct_0 @ X13)
% 0.40/0.57          | (v2_struct_0 @ X13)
% 0.40/0.57          | (v1_xboole_0 @ X14)
% 0.40/0.57          | ~ (v2_waybel_0 @ X14 @ (k3_yellow_1 @ X12))
% 0.40/0.57          | ~ (v13_waybel_0 @ X14 @ (k3_yellow_1 @ X12))
% 0.40/0.57          | ~ (m1_subset_1 @ X14 @ 
% 0.40/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X12))))
% 0.40/0.57          | (l1_waybel_0 @ (k3_yellow19 @ X13 @ X12 @ X14) @ X13))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.40/0.57  thf('83', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('84', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('85', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('86', plain,
% 0.40/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.40/0.57          | (v1_xboole_0 @ X12)
% 0.40/0.57          | ~ (l1_struct_0 @ X13)
% 0.40/0.57          | (v2_struct_0 @ X13)
% 0.40/0.57          | (v1_xboole_0 @ X14)
% 0.40/0.57          | ~ (v2_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.40/0.57          | ~ (v13_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.40/0.57          | ~ (m1_subset_1 @ X14 @ 
% 0.40/0.57               (k1_zfmisc_1 @ 
% 0.40/0.57                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X12)))))
% 0.40/0.57          | (l1_waybel_0 @ (k3_yellow19 @ X13 @ X12 @ X14) @ X13))),
% 0.40/0.57      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 0.40/0.57  thf('87', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.57          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | (v2_struct_0 @ X0)
% 0.40/0.57          | ~ (l1_struct_0 @ X0)
% 0.40/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['81', '86'])).
% 0.40/0.57  thf('88', plain,
% 0.40/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.57      inference('demod', [status(thm)], ['36', '37'])).
% 0.40/0.57  thf('89', plain,
% 0.40/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.57      inference('demod', [status(thm)], ['45', '46'])).
% 0.40/0.57  thf('90', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | (v2_struct_0 @ X0)
% 0.40/0.57          | ~ (l1_struct_0 @ X0)
% 0.40/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.57      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.40/0.57  thf('91', plain,
% 0.40/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57        | (v2_struct_0 @ sk_A)
% 0.40/0.57        | (v1_xboole_0 @ sk_B)
% 0.40/0.57        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.57           sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['80', '90'])).
% 0.40/0.57  thf('92', plain,
% 0.40/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.57        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.57           sk_A)
% 0.40/0.57        | (v1_xboole_0 @ sk_B)
% 0.40/0.57        | (v2_struct_0 @ sk_A)
% 0.40/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['79', '91'])).
% 0.40/0.57  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('94', plain,
% 0.40/0.57      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.57         sk_A)
% 0.40/0.57        | (v1_xboole_0 @ sk_B)
% 0.40/0.57        | (v2_struct_0 @ sk_A)
% 0.40/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('demod', [status(thm)], ['92', '93'])).
% 0.40/0.57  thf('95', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.57  thf('96', plain,
% 0.40/0.57      (![X5 : $i]:
% 0.40/0.57         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.57  thf('97', plain,
% 0.40/0.57      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.57        | (r2_hidden @ sk_C @ 
% 0.40/0.57           (k10_yellow_6 @ sk_A @ 
% 0.40/0.57            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('98', plain,
% 0.40/0.57      (((r2_hidden @ sk_C @ 
% 0.40/0.57         (k10_yellow_6 @ sk_A @ 
% 0.40/0.57          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.57         <= (((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('split', [status(esa)], ['97'])).
% 0.40/0.57  thf('99', plain,
% 0.40/0.57      ((((r2_hidden @ sk_C @ 
% 0.40/0.57          (k10_yellow_6 @ sk_A @ 
% 0.40/0.57           (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57         | ~ (l1_struct_0 @ sk_A)))
% 0.40/0.57         <= (((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('sup+', [status(thm)], ['96', '98'])).
% 0.40/0.57  thf('100', plain,
% 0.40/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.40/0.57         | (r2_hidden @ sk_C @ 
% 0.40/0.57            (k10_yellow_6 @ sk_A @ 
% 0.40/0.57             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))))
% 0.40/0.57         <= (((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['95', '99'])).
% 0.40/0.57  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('102', plain,
% 0.40/0.57      (((r2_hidden @ sk_C @ 
% 0.40/0.57         (k10_yellow_6 @ sk_A @ 
% 0.40/0.57          (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.57         <= (((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('demod', [status(thm)], ['100', '101'])).
% 0.40/0.57  thf(t13_yellow19, axiom,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.57       ( ![B:$i]:
% 0.40/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.40/0.57             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.40/0.57           ( ![C:$i]:
% 0.40/0.57             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.57               ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) <=>
% 0.40/0.57                 ( r2_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.40/0.57  thf('103', plain,
% 0.40/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.57         ((v2_struct_0 @ X21)
% 0.40/0.57          | ~ (v4_orders_2 @ X21)
% 0.40/0.57          | ~ (v7_waybel_0 @ X21)
% 0.40/0.57          | ~ (l1_waybel_0 @ X21 @ X22)
% 0.40/0.57          | ~ (r2_hidden @ X23 @ (k10_yellow_6 @ X22 @ X21))
% 0.40/0.57          | (r2_waybel_7 @ X22 @ (k2_yellow19 @ X22 @ X21) @ X23)
% 0.40/0.57          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.40/0.57          | ~ (l1_pre_topc @ X22)
% 0.40/0.57          | ~ (v2_pre_topc @ X22)
% 0.40/0.57          | (v2_struct_0 @ X22))),
% 0.40/0.57      inference('cnf', [status(esa)], [t13_yellow19])).
% 0.40/0.57  thf('104', plain,
% 0.40/0.57      ((((v2_struct_0 @ sk_A)
% 0.40/0.57         | ~ (v2_pre_topc @ sk_A)
% 0.40/0.57         | ~ (l1_pre_topc @ sk_A)
% 0.40/0.57         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.40/0.57         | (r2_waybel_7 @ sk_A @ 
% 0.40/0.57            (k2_yellow19 @ sk_A @ 
% 0.40/0.57             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.40/0.57            sk_C)
% 0.40/0.57         | ~ (l1_waybel_0 @ 
% 0.40/0.57              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.40/0.57         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.57         <= (((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['102', '103'])).
% 0.40/0.57  thf('105', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('107', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('108', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.57  thf('109', plain,
% 0.40/0.57      (![X5 : $i]:
% 0.40/0.57         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.57  thf('110', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.57  thf('111', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_B @ 
% 0.40/0.57        (k1_zfmisc_1 @ 
% 0.40/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.40/0.57  thf(t15_yellow19, axiom,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.40/0.57       ( ![B:$i]:
% 0.40/0.57         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.40/0.57             ( v1_subset_1 @
% 0.40/0.57               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.40/0.57             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.57             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.40/0.57             ( m1_subset_1 @
% 0.40/0.57               B @ 
% 0.40/0.57               ( k1_zfmisc_1 @
% 0.40/0.57                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.40/0.57           ( ( B ) =
% 0.40/0.57             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.40/0.57  thf('112', plain,
% 0.40/0.57      (![X24 : $i, X25 : $i]:
% 0.40/0.57         ((v1_xboole_0 @ X24)
% 0.40/0.57          | ~ (v1_subset_1 @ X24 @ 
% 0.40/0.57               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X25))))
% 0.40/0.57          | ~ (v2_waybel_0 @ X24 @ (k3_yellow_1 @ (k2_struct_0 @ X25)))
% 0.40/0.57          | ~ (v13_waybel_0 @ X24 @ (k3_yellow_1 @ (k2_struct_0 @ X25)))
% 0.40/0.57          | ~ (m1_subset_1 @ X24 @ 
% 0.40/0.57               (k1_zfmisc_1 @ 
% 0.40/0.57                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X25)))))
% 0.40/0.57          | ((X24)
% 0.40/0.57              = (k2_yellow19 @ X25 @ 
% 0.40/0.57                 (k3_yellow19 @ X25 @ (k2_struct_0 @ X25) @ X24)))
% 0.40/0.57          | ~ (l1_struct_0 @ X25)
% 0.40/0.57          | (v2_struct_0 @ X25))),
% 0.40/0.57      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.40/0.57  thf('113', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('114', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('115', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('116', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('117', plain,
% 0.40/0.57      (![X24 : $i, X25 : $i]:
% 0.40/0.57         ((v1_xboole_0 @ X24)
% 0.40/0.57          | ~ (v1_subset_1 @ X24 @ 
% 0.40/0.57               (u1_struct_0 @ 
% 0.40/0.57                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X25)))))
% 0.40/0.57          | ~ (v2_waybel_0 @ X24 @ 
% 0.40/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X25))))
% 0.40/0.57          | ~ (v13_waybel_0 @ X24 @ 
% 0.40/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X25))))
% 0.40/0.57          | ~ (m1_subset_1 @ X24 @ 
% 0.40/0.57               (k1_zfmisc_1 @ 
% 0.40/0.57                (u1_struct_0 @ 
% 0.40/0.57                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X25))))))
% 0.40/0.57          | ((X24)
% 0.40/0.57              = (k2_yellow19 @ X25 @ 
% 0.40/0.57                 (k3_yellow19 @ X25 @ (k2_struct_0 @ X25) @ X24)))
% 0.40/0.57          | ~ (l1_struct_0 @ X25)
% 0.40/0.57          | (v2_struct_0 @ X25))),
% 0.40/0.57      inference('demod', [status(thm)], ['112', '113', '114', '115', '116'])).
% 0.40/0.57  thf('118', plain,
% 0.40/0.57      (((v2_struct_0 @ sk_A)
% 0.40/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57        | ((sk_B)
% 0.40/0.57            = (k2_yellow19 @ sk_A @ 
% 0.40/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57        | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.57             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.57        | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.57             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.57        | ~ (v1_subset_1 @ sk_B @ 
% 0.40/0.57             (u1_struct_0 @ 
% 0.40/0.57              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.40/0.57        | (v1_xboole_0 @ sk_B))),
% 0.40/0.57      inference('sup-', [status(thm)], ['111', '117'])).
% 0.40/0.57  thf('119', plain,
% 0.40/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.40/0.57  thf('120', plain,
% 0.40/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.57      inference('demod', [status(thm)], ['41', '42'])).
% 0.40/0.57  thf('121', plain,
% 0.40/0.57      ((v1_subset_1 @ sk_B @ 
% 0.40/0.57        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.40/0.57      inference('demod', [status(thm)], ['67', '68'])).
% 0.40/0.57  thf('122', plain,
% 0.40/0.57      (((v2_struct_0 @ sk_A)
% 0.40/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57        | ((sk_B)
% 0.40/0.57            = (k2_yellow19 @ sk_A @ 
% 0.40/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57        | (v1_xboole_0 @ sk_B))),
% 0.40/0.57      inference('demod', [status(thm)], ['118', '119', '120', '121'])).
% 0.40/0.57  thf('123', plain,
% 0.40/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.57        | (v1_xboole_0 @ sk_B)
% 0.40/0.57        | ((sk_B)
% 0.40/0.57            = (k2_yellow19 @ sk_A @ 
% 0.40/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57        | (v2_struct_0 @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['110', '122'])).
% 0.40/0.57  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('125', plain,
% 0.40/0.57      (((v1_xboole_0 @ sk_B)
% 0.40/0.57        | ((sk_B)
% 0.40/0.57            = (k2_yellow19 @ sk_A @ 
% 0.40/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57        | (v2_struct_0 @ sk_A))),
% 0.40/0.57      inference('demod', [status(thm)], ['123', '124'])).
% 0.40/0.57  thf('126', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('127', plain,
% 0.40/0.57      (((v2_struct_0 @ sk_A)
% 0.40/0.57        | ((sk_B)
% 0.40/0.57            = (k2_yellow19 @ sk_A @ 
% 0.40/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.40/0.57      inference('clc', [status(thm)], ['125', '126'])).
% 0.40/0.57  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('129', plain,
% 0.40/0.57      (((sk_B)
% 0.40/0.57         = (k2_yellow19 @ sk_A @ 
% 0.40/0.57            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.57      inference('clc', [status(thm)], ['127', '128'])).
% 0.40/0.57  thf('130', plain,
% 0.40/0.57      ((((sk_B)
% 0.40/0.57          = (k2_yellow19 @ sk_A @ 
% 0.40/0.57             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.57      inference('sup+', [status(thm)], ['109', '129'])).
% 0.40/0.57  thf('131', plain,
% 0.40/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.57        | ((sk_B)
% 0.40/0.57            = (k2_yellow19 @ sk_A @ 
% 0.40/0.57               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['108', '130'])).
% 0.40/0.57  thf('132', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('133', plain,
% 0.40/0.57      (((sk_B)
% 0.40/0.57         = (k2_yellow19 @ sk_A @ 
% 0.40/0.57            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.57      inference('demod', [status(thm)], ['131', '132'])).
% 0.40/0.57  thf('134', plain,
% 0.40/0.57      ((((v2_struct_0 @ sk_A)
% 0.40/0.57         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.57         | ~ (l1_waybel_0 @ 
% 0.40/0.57              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.40/0.57         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.57         <= (((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('demod', [status(thm)], ['104', '105', '106', '107', '133'])).
% 0.40/0.57  thf('135', plain,
% 0.40/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ sk_B)
% 0.40/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.57         | (v2_struct_0 @ sk_A)))
% 0.40/0.57         <= (((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['94', '134'])).
% 0.40/0.57  thf('136', plain,
% 0.40/0.57      ((((r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.57         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57         | (v1_xboole_0 @ sk_B)
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57         <= (((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('simplify', [status(thm)], ['135'])).
% 0.40/0.57  thf('137', plain,
% 0.40/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ sk_B)
% 0.40/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ sk_B)
% 0.40/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.40/0.57         <= (((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['78', '136'])).
% 0.40/0.57  thf('138', plain,
% 0.40/0.57      ((((r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.57         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57         | (v1_xboole_0 @ sk_B)
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57         <= (((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('simplify', [status(thm)], ['137'])).
% 0.40/0.57  thf('139', plain,
% 0.40/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ sk_B)
% 0.40/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ sk_B)
% 0.40/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.40/0.57         <= (((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['52', '138'])).
% 0.40/0.57  thf('140', plain,
% 0.40/0.57      ((((r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57         | (v1_xboole_0 @ sk_B)
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57         <= (((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('simplify', [status(thm)], ['139'])).
% 0.40/0.57  thf('141', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.40/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.40/0.57  thf('142', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_B @ 
% 0.40/0.57        (k1_zfmisc_1 @ 
% 0.40/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.40/0.57      inference('demod', [status(thm)], ['21', '22'])).
% 0.40/0.57  thf('143', plain,
% 0.40/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.40/0.57          | (v1_xboole_0 @ X12)
% 0.40/0.57          | ~ (l1_struct_0 @ X13)
% 0.40/0.57          | (v2_struct_0 @ X13)
% 0.40/0.57          | (v1_xboole_0 @ X14)
% 0.40/0.57          | ~ (v2_waybel_0 @ X14 @ (k3_yellow_1 @ X12))
% 0.40/0.57          | ~ (v13_waybel_0 @ X14 @ (k3_yellow_1 @ X12))
% 0.40/0.57          | ~ (m1_subset_1 @ X14 @ 
% 0.40/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X12))))
% 0.40/0.57          | ~ (v2_struct_0 @ (k3_yellow19 @ X13 @ X12 @ X14)))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.40/0.57  thf('144', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('145', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('146', plain,
% 0.40/0.57      (![X11 : $i]: ((k3_yellow_1 @ X11) = (k3_lattice3 @ (k1_lattice3 @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.40/0.57  thf('147', plain,
% 0.40/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.40/0.57          | (v1_xboole_0 @ X12)
% 0.40/0.57          | ~ (l1_struct_0 @ X13)
% 0.40/0.57          | (v2_struct_0 @ X13)
% 0.40/0.57          | (v1_xboole_0 @ X14)
% 0.40/0.57          | ~ (v2_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.40/0.57          | ~ (v13_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.40/0.57          | ~ (m1_subset_1 @ X14 @ 
% 0.40/0.57               (k1_zfmisc_1 @ 
% 0.40/0.57                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X12)))))
% 0.40/0.57          | ~ (v2_struct_0 @ (k3_yellow19 @ X13 @ X12 @ X14)))),
% 0.40/0.57      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 0.40/0.57  thf('148', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.57               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | (v2_struct_0 @ X0)
% 0.40/0.57          | ~ (l1_struct_0 @ X0)
% 0.40/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['142', '147'])).
% 0.40/0.57  thf('149', plain,
% 0.40/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.57      inference('demod', [status(thm)], ['36', '37'])).
% 0.40/0.57  thf('150', plain,
% 0.40/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.57        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.57      inference('demod', [status(thm)], ['45', '46'])).
% 0.40/0.57  thf('151', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | (v2_struct_0 @ X0)
% 0.40/0.57          | ~ (l1_struct_0 @ X0)
% 0.40/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.57      inference('demod', [status(thm)], ['148', '149', '150'])).
% 0.40/0.57  thf('152', plain,
% 0.40/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57        | (v2_struct_0 @ sk_A)
% 0.40/0.57        | (v1_xboole_0 @ sk_B)
% 0.40/0.57        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['141', '151'])).
% 0.40/0.57  thf('153', plain,
% 0.40/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ sk_B)
% 0.40/0.57         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.57         | (v1_xboole_0 @ sk_B)
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57         <= (((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['140', '152'])).
% 0.40/0.57  thf('154', plain,
% 0.40/0.57      (((~ (l1_struct_0 @ sk_A)
% 0.40/0.57         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.40/0.57         | (v1_xboole_0 @ sk_B)
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57         <= (((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('simplify', [status(thm)], ['153'])).
% 0.40/0.57  thf('155', plain,
% 0.40/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ sk_B)
% 0.40/0.57         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.40/0.57         <= (((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['10', '154'])).
% 0.40/0.57  thf('156', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('157', plain,
% 0.40/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ sk_B)
% 0.40/0.57         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.40/0.57         <= (((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('demod', [status(thm)], ['155', '156'])).
% 0.40/0.57  thf('158', plain,
% 0.40/0.57      ((~ (r2_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.40/0.57         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.57      inference('split', [status(esa)], ['0'])).
% 0.40/0.57  thf('159', plain,
% 0.40/0.57      ((((v1_xboole_0 @ sk_B)
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.57             ((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['157', '158'])).
% 0.40/0.57  thf('160', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('161', plain,
% 0.40/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.40/0.57         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.57             ((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('clc', [status(thm)], ['159', '160'])).
% 0.40/0.57  thf('162', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('163', plain,
% 0.40/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.40/0.57         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.57             ((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('clc', [status(thm)], ['161', '162'])).
% 0.40/0.57  thf('164', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(dt_k1_connsp_2, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.40/0.57         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.57       ( m1_subset_1 @
% 0.40/0.57         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.40/0.57  thf('165', plain,
% 0.40/0.57      (![X7 : $i, X8 : $i]:
% 0.40/0.57         (~ (l1_pre_topc @ X7)
% 0.40/0.57          | ~ (v2_pre_topc @ X7)
% 0.40/0.57          | (v2_struct_0 @ X7)
% 0.40/0.57          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.40/0.57          | (m1_subset_1 @ (k1_connsp_2 @ X7 @ X8) @ 
% 0.40/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.40/0.57  thf('166', plain,
% 0.40/0.57      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_C) @ 
% 0.40/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.57        | (v2_struct_0 @ sk_A)
% 0.40/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.40/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['164', '165'])).
% 0.40/0.57  thf('167', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('169', plain,
% 0.40/0.57      (((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_C) @ 
% 0.40/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.57        | (v2_struct_0 @ sk_A))),
% 0.40/0.57      inference('demod', [status(thm)], ['166', '167', '168'])).
% 0.40/0.57  thf('170', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('171', plain,
% 0.40/0.57      ((m1_subset_1 @ (k1_connsp_2 @ sk_A @ sk_C) @ 
% 0.40/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('clc', [status(thm)], ['169', '170'])).
% 0.40/0.57  thf(t5_subset, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.40/0.57          ( v1_xboole_0 @ C ) ) ))).
% 0.40/0.57  thf('172', plain,
% 0.40/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.57         (~ (r2_hidden @ X2 @ X3)
% 0.40/0.57          | ~ (v1_xboole_0 @ X4)
% 0.40/0.57          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t5_subset])).
% 0.40/0.57  thf('173', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_A @ sk_C)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['171', '172'])).
% 0.40/0.57  thf('174', plain,
% 0.40/0.57      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_A @ sk_C)))
% 0.40/0.57         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.40/0.57             ((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['163', '173'])).
% 0.40/0.57  thf('175', plain,
% 0.40/0.57      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.40/0.57       ~
% 0.40/0.57       ((r2_hidden @ sk_C @ 
% 0.40/0.57         (k10_yellow_6 @ sk_A @ 
% 0.40/0.57          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['9', '174'])).
% 0.40/0.57  thf('176', plain,
% 0.40/0.57      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.40/0.57       ((r2_hidden @ sk_C @ 
% 0.40/0.57         (k10_yellow_6 @ sk_A @ 
% 0.40/0.57          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.40/0.57      inference('split', [status(esa)], ['97'])).
% 0.40/0.57  thf('177', plain, ((r2_hidden @ sk_C @ (k1_connsp_2 @ sk_A @ sk_C))),
% 0.40/0.57      inference('clc', [status(thm)], ['7', '8'])).
% 0.40/0.57  thf('178', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.57  thf('179', plain,
% 0.40/0.57      (![X5 : $i]:
% 0.40/0.57         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.57  thf('180', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.57  thf('181', plain,
% 0.40/0.57      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.40/0.57         <= (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.57      inference('split', [status(esa)], ['97'])).
% 0.40/0.57  thf('182', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.57  thf('183', plain,
% 0.40/0.57      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57        | (v1_xboole_0 @ sk_B)
% 0.40/0.57        | (v2_struct_0 @ sk_A)
% 0.40/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('demod', [status(thm)], ['76', '77'])).
% 0.40/0.57  thf('184', plain,
% 0.40/0.57      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57        | (v1_xboole_0 @ sk_B)
% 0.40/0.57        | (v2_struct_0 @ sk_A)
% 0.40/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('demod', [status(thm)], ['50', '51'])).
% 0.40/0.57  thf('185', plain,
% 0.40/0.57      (![X5 : $i]:
% 0.40/0.57         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.57  thf('186', plain,
% 0.40/0.57      (![X5 : $i]:
% 0.40/0.57         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.57  thf('187', plain,
% 0.40/0.57      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.40/0.57         sk_A)
% 0.40/0.57        | (v1_xboole_0 @ sk_B)
% 0.40/0.57        | (v2_struct_0 @ sk_A)
% 0.40/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('demod', [status(thm)], ['92', '93'])).
% 0.40/0.57  thf('188', plain,
% 0.40/0.57      (![X5 : $i]:
% 0.40/0.57         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.57  thf('189', plain,
% 0.40/0.57      (((sk_B)
% 0.40/0.57         = (k2_yellow19 @ sk_A @ 
% 0.40/0.57            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.57      inference('clc', [status(thm)], ['127', '128'])).
% 0.40/0.57  thf('190', plain,
% 0.40/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.57         ((v2_struct_0 @ X21)
% 0.40/0.57          | ~ (v4_orders_2 @ X21)
% 0.40/0.57          | ~ (v7_waybel_0 @ X21)
% 0.40/0.57          | ~ (l1_waybel_0 @ X21 @ X22)
% 0.40/0.57          | ~ (r2_waybel_7 @ X22 @ (k2_yellow19 @ X22 @ X21) @ X23)
% 0.40/0.57          | (r2_hidden @ X23 @ (k10_yellow_6 @ X22 @ X21))
% 0.40/0.57          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.40/0.57          | ~ (l1_pre_topc @ X22)
% 0.40/0.57          | ~ (v2_pre_topc @ X22)
% 0.40/0.57          | (v2_struct_0 @ X22))),
% 0.40/0.57      inference('cnf', [status(esa)], [t13_yellow19])).
% 0.40/0.57  thf('191', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.57          | (v2_struct_0 @ sk_A)
% 0.40/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.40/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | (r2_hidden @ X0 @ 
% 0.40/0.57             (k10_yellow_6 @ sk_A @ 
% 0.40/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57          | ~ (l1_waybel_0 @ 
% 0.40/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.40/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['189', '190'])).
% 0.40/0.57  thf('192', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('193', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('194', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.57          | (v2_struct_0 @ sk_A)
% 0.40/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | (r2_hidden @ X0 @ 
% 0.40/0.57             (k10_yellow_6 @ sk_A @ 
% 0.40/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57          | ~ (l1_waybel_0 @ 
% 0.40/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.40/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.57      inference('demod', [status(thm)], ['191', '192', '193'])).
% 0.40/0.57  thf('195', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (l1_waybel_0 @ 
% 0.40/0.57             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.40/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | (r2_hidden @ X0 @ 
% 0.40/0.57             (k10_yellow_6 @ sk_A @ 
% 0.40/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | (v2_struct_0 @ sk_A)
% 0.40/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['188', '194'])).
% 0.40/0.57  thf('196', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | (v2_struct_0 @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.57          | (v2_struct_0 @ sk_A)
% 0.40/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | (r2_hidden @ X0 @ 
% 0.40/0.57             (k10_yellow_6 @ sk_A @ 
% 0.40/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['187', '195'])).
% 0.40/0.57  thf('197', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (l1_struct_0 @ sk_A)
% 0.40/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | (r2_hidden @ X0 @ 
% 0.40/0.57             (k10_yellow_6 @ sk_A @ 
% 0.40/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | (v2_struct_0 @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['196'])).
% 0.40/0.57  thf('198', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | (v2_struct_0 @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | (r2_hidden @ X0 @ 
% 0.40/0.57             (k10_yellow_6 @ sk_A @ 
% 0.40/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['186', '197'])).
% 0.40/0.57  thf('199', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | (r2_hidden @ X0 @ 
% 0.40/0.57             (k10_yellow_6 @ sk_A @ 
% 0.40/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | (v2_struct_0 @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['198'])).
% 0.40/0.57  thf('200', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | (v2_struct_0 @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | (r2_hidden @ X0 @ 
% 0.40/0.57             (k10_yellow_6 @ sk_A @ 
% 0.40/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['185', '199'])).
% 0.40/0.57  thf('201', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | (r2_hidden @ X0 @ 
% 0.40/0.57             (k10_yellow_6 @ sk_A @ 
% 0.40/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | (v2_struct_0 @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['200'])).
% 0.40/0.57  thf('202', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | (v2_struct_0 @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | (v2_struct_0 @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | (r2_hidden @ X0 @ 
% 0.40/0.57             (k10_yellow_6 @ sk_A @ 
% 0.40/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['184', '201'])).
% 0.40/0.57  thf('203', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | (r2_hidden @ X0 @ 
% 0.40/0.57             (k10_yellow_6 @ sk_A @ 
% 0.40/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | (v2_struct_0 @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['202'])).
% 0.40/0.57  thf('204', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | (v2_struct_0 @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | (v2_struct_0 @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | (r2_hidden @ X0 @ 
% 0.40/0.57             (k10_yellow_6 @ sk_A @ 
% 0.40/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['183', '203'])).
% 0.40/0.57  thf('205', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | (r2_hidden @ X0 @ 
% 0.40/0.57             (k10_yellow_6 @ sk_A @ 
% 0.40/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | (v2_struct_0 @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['204'])).
% 0.40/0.57  thf('206', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (l1_pre_topc @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | (v2_struct_0 @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | (r2_hidden @ X0 @ 
% 0.40/0.57             (k10_yellow_6 @ sk_A @ 
% 0.40/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['182', '205'])).
% 0.40/0.57  thf('207', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('208', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | (v2_struct_0 @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.40/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | (r2_hidden @ X0 @ 
% 0.40/0.57             (k10_yellow_6 @ sk_A @ 
% 0.40/0.57              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.57      inference('demod', [status(thm)], ['206', '207'])).
% 0.40/0.57  thf('209', plain,
% 0.40/0.57      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57         | (r2_hidden @ sk_C @ 
% 0.40/0.57            (k10_yellow_6 @ sk_A @ 
% 0.40/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.40/0.57         | (v1_xboole_0 @ sk_B)
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57         <= (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['181', '208'])).
% 0.40/0.57  thf('210', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('211', plain,
% 0.40/0.57      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57         | (r2_hidden @ sk_C @ 
% 0.40/0.57            (k10_yellow_6 @ sk_A @ 
% 0.40/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.40/0.57         | (v1_xboole_0 @ sk_B)
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57         <= (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.57      inference('demod', [status(thm)], ['209', '210'])).
% 0.40/0.57  thf('212', plain,
% 0.40/0.57      ((~ (r2_hidden @ sk_C @ 
% 0.40/0.57           (k10_yellow_6 @ sk_A @ 
% 0.40/0.57            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.57         <= (~
% 0.40/0.57             ((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.40/0.57      inference('split', [status(esa)], ['0'])).
% 0.40/0.57  thf('213', plain,
% 0.40/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ sk_B)
% 0.40/0.57         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.40/0.57         <= (~
% 0.40/0.57             ((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.40/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['211', '212'])).
% 0.40/0.57  thf('214', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.40/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.40/0.57  thf('215', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.57  thf('216', plain,
% 0.40/0.57      (![X5 : $i]:
% 0.40/0.57         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.57  thf('217', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_B @ 
% 0.40/0.57        (k1_zfmisc_1 @ 
% 0.40/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.40/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.40/0.57  thf('218', plain,
% 0.40/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.40/0.57          | (v1_xboole_0 @ X12)
% 0.40/0.57          | ~ (l1_struct_0 @ X13)
% 0.40/0.57          | (v2_struct_0 @ X13)
% 0.40/0.57          | (v1_xboole_0 @ X14)
% 0.40/0.57          | ~ (v2_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.40/0.57          | ~ (v13_waybel_0 @ X14 @ (k3_lattice3 @ (k1_lattice3 @ X12)))
% 0.40/0.57          | ~ (m1_subset_1 @ X14 @ 
% 0.40/0.57               (k1_zfmisc_1 @ 
% 0.40/0.57                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X12)))))
% 0.40/0.57          | ~ (v2_struct_0 @ (k3_yellow19 @ X13 @ X12 @ X14)))),
% 0.40/0.57      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 0.40/0.57  thf('219', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | ~ (v13_waybel_0 @ sk_B @ 
% 0.40/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.57          | ~ (v2_waybel_0 @ sk_B @ 
% 0.40/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | (v2_struct_0 @ X0)
% 0.40/0.57          | ~ (l1_struct_0 @ X0)
% 0.40/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.57          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['217', '218'])).
% 0.40/0.57  thf('220', plain,
% 0.40/0.57      ((v13_waybel_0 @ sk_B @ 
% 0.40/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.40/0.57  thf('221', plain,
% 0.40/0.57      ((v2_waybel_0 @ sk_B @ 
% 0.40/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.40/0.57      inference('demod', [status(thm)], ['41', '42'])).
% 0.40/0.57  thf('222', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | (v2_struct_0 @ X0)
% 0.40/0.57          | ~ (l1_struct_0 @ X0)
% 0.40/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.57          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.57      inference('demod', [status(thm)], ['219', '220', '221'])).
% 0.40/0.57  thf('223', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.40/0.57          | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.57          | ~ (l1_struct_0 @ X0)
% 0.40/0.57          | (v2_struct_0 @ X0)
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['216', '222'])).
% 0.40/0.57  thf('224', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (l1_pre_topc @ sk_A)
% 0.40/0.57          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | (v2_struct_0 @ X0)
% 0.40/0.57          | ~ (l1_struct_0 @ X0)
% 0.40/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['215', '223'])).
% 0.40/0.57  thf('225', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('226', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.40/0.57          | (v1_xboole_0 @ sk_B)
% 0.40/0.57          | (v2_struct_0 @ X0)
% 0.40/0.57          | ~ (l1_struct_0 @ X0)
% 0.40/0.57          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.40/0.57      inference('demod', [status(thm)], ['224', '225'])).
% 0.40/0.57  thf('227', plain,
% 0.40/0.57      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57        | (v2_struct_0 @ sk_A)
% 0.40/0.57        | (v1_xboole_0 @ sk_B)
% 0.40/0.57        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['214', '226'])).
% 0.40/0.57  thf('228', plain,
% 0.40/0.57      ((((v1_xboole_0 @ sk_B)
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57         | (v1_xboole_0 @ sk_B)
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.40/0.57         <= (~
% 0.40/0.57             ((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.40/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['213', '227'])).
% 0.40/0.57  thf('229', plain,
% 0.40/0.57      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.40/0.57         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ sk_B)))
% 0.40/0.57         <= (~
% 0.40/0.57             ((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.40/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['228'])).
% 0.40/0.57  thf('230', plain,
% 0.40/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ sk_B)
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.40/0.57         <= (~
% 0.40/0.57             ((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.40/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['180', '229'])).
% 0.40/0.57  thf('231', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('232', plain,
% 0.40/0.57      ((((v1_xboole_0 @ sk_B)
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.40/0.57         <= (~
% 0.40/0.57             ((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.40/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.57      inference('demod', [status(thm)], ['230', '231'])).
% 0.40/0.57  thf('233', plain,
% 0.40/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ sk_B)))
% 0.40/0.57         <= (~
% 0.40/0.57             ((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.40/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.57      inference('sup+', [status(thm)], ['179', '232'])).
% 0.40/0.57  thf('234', plain,
% 0.40/0.57      ((((v1_xboole_0 @ sk_B)
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | ~ (l1_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57         <= (~
% 0.40/0.57             ((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.40/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['233'])).
% 0.40/0.57  thf('235', plain,
% 0.40/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ sk_B)))
% 0.40/0.57         <= (~
% 0.40/0.57             ((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.40/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['178', '234'])).
% 0.40/0.57  thf('236', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('237', plain,
% 0.40/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57         | (v2_struct_0 @ sk_A)
% 0.40/0.57         | (v1_xboole_0 @ sk_B)))
% 0.40/0.57         <= (~
% 0.40/0.57             ((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.40/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.57      inference('demod', [status(thm)], ['235', '236'])).
% 0.40/0.57  thf('238', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('239', plain,
% 0.40/0.57      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.40/0.57         <= (~
% 0.40/0.57             ((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.40/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.57      inference('clc', [status(thm)], ['237', '238'])).
% 0.40/0.57  thf('240', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('241', plain,
% 0.40/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.40/0.57         <= (~
% 0.40/0.57             ((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.40/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.57      inference('clc', [status(thm)], ['239', '240'])).
% 0.40/0.57  thf('242', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.57          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_A @ sk_C)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['171', '172'])).
% 0.40/0.57  thf('243', plain,
% 0.40/0.57      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_A @ sk_C)))
% 0.40/0.57         <= (~
% 0.40/0.57             ((r2_hidden @ sk_C @ 
% 0.40/0.57               (k10_yellow_6 @ sk_A @ 
% 0.40/0.57                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.40/0.57             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['241', '242'])).
% 0.40/0.57  thf('244', plain,
% 0.40/0.57      (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.40/0.57       ((r2_hidden @ sk_C @ 
% 0.40/0.57         (k10_yellow_6 @ sk_A @ 
% 0.40/0.57          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['177', '243'])).
% 0.40/0.57  thf('245', plain, ($false),
% 0.40/0.57      inference('sat_resolution*', [status(thm)], ['1', '175', '176', '244'])).
% 0.40/0.57  
% 0.40/0.57  % SZS output end Refutation
% 0.40/0.57  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
