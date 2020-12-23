%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2059+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dFpnx0Sy8v

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:44 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 401 expanded)
%              Number of leaves         :   35 ( 128 expanded)
%              Depth                    :   30
%              Number of atoms          : 2575 (10253 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

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
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v2_waybel_0 @ X7 @ ( k3_yellow_1 @ X5 ) )
      | ~ ( v13_waybel_0 @ X7 @ ( k3_yellow_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X5 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X6 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_subset_1 @ X11 @ ( u1_struct_0 @ ( k3_yellow_1 @ X9 ) ) )
      | ~ ( v2_waybel_0 @ X11 @ ( k3_yellow_1 @ X9 ) )
      | ~ ( v13_waybel_0 @ X11 @ ( k3_yellow_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X9 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X10 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('34',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v2_waybel_0 @ X3 @ ( k3_yellow_1 @ X1 ) )
      | ~ ( v13_waybel_0 @ X3 @ ( k3_yellow_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X1 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X2 @ X1 @ X3 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['44'])).

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

thf('46',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v7_waybel_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( r2_hidden @ X14 @ ( k10_yellow_6 @ X13 @ X12 ) )
      | ( r2_waybel_7 @ X13 @ ( k2_yellow19 @ X13 @ X12 ) @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow19])).

thf('47',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r2_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('53',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( v1_subset_1 @ X15 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X16 ) ) ) )
      | ~ ( v2_waybel_0 @ X15 @ ( k3_yellow_1 @ ( k2_struct_0 @ X16 ) ) )
      | ~ ( v13_waybel_0 @ X15 @ ( k3_yellow_1 @ ( k2_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X16 ) ) ) ) )
      | ( X15
        = ( k2_yellow19 @ X16 @ ( k3_yellow19 @ X16 @ ( k2_struct_0 @ X16 ) @ X15 ) ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','65'])).

thf('67',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','66'])).

thf('68',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','68'])).

thf('70',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','70'])).

thf('72',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v2_waybel_0 @ X3 @ ( k3_yellow_1 @ X1 ) )
      | ~ ( v13_waybel_0 @ X3 @ ( k3_yellow_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X1 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X2 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
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
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','79'])).

thf('81',plain,
    ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['72','81'])).

thf('83',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('88',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('93',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('94',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['2','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['44'])).

thf('101',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('102',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('103',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['44'])).

thf('104',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('105',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('106',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('107',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('108',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v7_waybel_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( r2_waybel_7 @ X13 @ ( k2_yellow19 @ X13 @ X12 ) @ X14 )
      | ( r2_hidden @ X14 @ ( k10_yellow_6 @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow19])).

thf('109',plain,(
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
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['103','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('123',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['80'])).

thf('125',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['102','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('135',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['101','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','99','100','140'])).


%------------------------------------------------------------------------------
