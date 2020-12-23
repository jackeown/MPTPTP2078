%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yyyUJULPZd

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:54 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 421 expanded)
%              Number of leaves         :   36 ( 134 expanded)
%              Depth                    :   33
%              Number of atoms          : 2712 (10597 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('5',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v2_waybel_0 @ X9 @ ( k3_yellow_1 @ X7 ) )
      | ~ ( v13_waybel_0 @ X9 @ ( k3_yellow_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X7 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X8 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v1_subset_1 @ X12 @ ( u1_struct_0 @ ( k3_yellow_1 @ X10 ) ) )
      | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ X10 ) )
      | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X10 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('23',plain,(
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
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v2_waybel_0 @ X6 @ ( k3_yellow_1 @ X4 ) )
      | ~ ( v13_waybel_0 @ X6 @ ( k3_yellow_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X4 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X5 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['46'])).

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

thf('48',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v7_waybel_0 @ X13 )
      | ~ ( l1_waybel_0 @ X13 @ X14 )
      | ~ ( r2_hidden @ X15 @ ( k10_yellow_6 @ X14 @ X13 ) )
      | ( r2_waybel_7 @ X14 @ ( k2_yellow19 @ X14 @ X13 ) @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow19])).

thf('49',plain,
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
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
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

thf('55',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( v1_subset_1 @ X16 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X17 ) ) ) )
      | ~ ( v2_waybel_0 @ X16 @ ( k3_yellow_1 @ ( k2_struct_0 @ X17 ) ) )
      | ~ ( v13_waybel_0 @ X16 @ ( k3_yellow_1 @ ( k2_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X17 ) ) ) ) )
      | ( X16
        = ( k2_yellow19 @ X17 @ ( k3_yellow19 @ X17 @ ( k2_struct_0 @ X17 ) @ X16 ) ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','67'])).

thf('69',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','68'])).

thf('70',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
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
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','70'])).

thf('72',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','72'])).

thf('74',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v2_waybel_0 @ X6 @ ( k3_yellow_1 @ X4 ) )
      | ~ ( v13_waybel_0 @ X6 @ ( k3_yellow_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X4 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X5 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','81'])).

thf('83',plain,
    ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','83'])).

thf('85',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('90',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['4','94'])).

thf('96',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['3','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('99',plain,(
    ! [X3: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('100',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['2','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['46'])).

thf('107',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('108',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('110',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('111',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['46'])).

thf('112',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('113',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('114',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('115',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('116',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v7_waybel_0 @ X13 )
      | ~ ( l1_waybel_0 @ X13 @ X14 )
      | ~ ( r2_waybel_7 @ X14 @ ( k2_yellow19 @ X14 @ X13 ) @ X15 )
      | ( r2_hidden @ X15 @ ( k10_yellow_6 @ X14 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow19])).

thf('117',plain,(
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
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
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
    inference('sup-',[status(thm)],['114','120'])).

thf('122',plain,(
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
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
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
    inference('sup-',[status(thm)],['113','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
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
    inference('sup-',[status(thm)],['112','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['111','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('131',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['82'])).

thf('133',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['110','134'])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['109','141'])).

thf('143',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['108','142'])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X3: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('147',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['107','149'])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','105','106','152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yyyUJULPZd
% 0.12/0.37  % Computer   : n015.cluster.edu
% 0.12/0.37  % Model      : x86_64 x86_64
% 0.12/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.37  % Memory     : 8042.1875MB
% 0.12/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.37  % CPULimit   : 60
% 0.12/0.37  % DateTime   : Tue Dec  1 18:33:38 EST 2020
% 0.12/0.37  % CPUTime    : 
% 0.12/0.37  % Running portfolio for 600 s
% 0.12/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.37  % Number of cores: 8
% 0.12/0.37  % Python version: Python 3.6.8
% 0.12/0.37  % Running in FO mode
% 0.44/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.63  % Solved by: fo/fo7.sh
% 0.44/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.63  % done 219 iterations in 0.144s
% 0.44/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.63  % SZS output start Refutation
% 0.44/0.63  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.44/0.63  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.44/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.63  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.44/0.63  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.44/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.63  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.44/0.63  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.44/0.63  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.44/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.63  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.44/0.63  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.44/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.44/0.63  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.44/0.63  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.44/0.63  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.44/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.44/0.63  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.44/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.44/0.63  thf(r2_waybel_7_type, type, r2_waybel_7: $i > $i > $i > $o).
% 0.44/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.63  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.44/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.63  thf(t18_yellow19, conjecture,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.63       ( ![B:$i]:
% 0.44/0.63         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.44/0.63             ( v1_subset_1 @
% 0.44/0.63               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.44/0.63             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.44/0.63             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.44/0.63             ( m1_subset_1 @
% 0.44/0.63               B @ 
% 0.44/0.63               ( k1_zfmisc_1 @
% 0.44/0.63                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.44/0.63           ( ![C:$i]:
% 0.44/0.63             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.63               ( ( r2_hidden @
% 0.44/0.63                   C @ 
% 0.44/0.63                   ( k10_yellow_6 @
% 0.44/0.63                     A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) <=>
% 0.44/0.63                 ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.44/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.63    (~( ![A:$i]:
% 0.44/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.44/0.63            ( l1_pre_topc @ A ) ) =>
% 0.44/0.63          ( ![B:$i]:
% 0.44/0.63            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.44/0.63                ( v1_subset_1 @
% 0.44/0.63                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.44/0.63                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.44/0.63                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.44/0.63                ( m1_subset_1 @
% 0.44/0.63                  B @ 
% 0.44/0.63                  ( k1_zfmisc_1 @
% 0.44/0.63                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.44/0.63              ( ![C:$i]:
% 0.44/0.63                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.63                  ( ( r2_hidden @
% 0.44/0.63                      C @ 
% 0.44/0.63                      ( k10_yellow_6 @
% 0.44/0.63                        A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) <=>
% 0.44/0.63                    ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.44/0.63    inference('cnf.neg', [status(esa)], [t18_yellow19])).
% 0.44/0.63  thf('0', plain,
% 0.44/0.63      ((~ (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.44/0.63        | ~ (r2_hidden @ sk_C @ 
% 0.44/0.63             (k10_yellow_6 @ sk_A @ 
% 0.44/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('1', plain,
% 0.44/0.63      (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.44/0.63       ~
% 0.44/0.63       ((r2_hidden @ sk_C @ 
% 0.44/0.63         (k10_yellow_6 @ sk_A @ 
% 0.44/0.63          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.44/0.63      inference('split', [status(esa)], ['0'])).
% 0.44/0.63  thf(dt_l1_pre_topc, axiom,
% 0.44/0.63    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.44/0.63  thf('2', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.44/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.44/0.63  thf('3', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.44/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.44/0.63  thf(d3_struct_0, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.44/0.63  thf('4', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.44/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.63  thf('5', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.44/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.44/0.63  thf('6', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.44/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.44/0.63  thf(dt_k2_struct_0, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( l1_struct_0 @ A ) =>
% 0.44/0.63       ( m1_subset_1 @
% 0.44/0.63         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.44/0.63  thf('7', plain,
% 0.44/0.63      (![X1 : $i]:
% 0.44/0.63         ((m1_subset_1 @ (k2_struct_0 @ X1) @ 
% 0.47/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.47/0.63          | ~ (l1_struct_0 @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.47/0.63  thf('8', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B @ 
% 0.47/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(fc4_yellow19, axiom,
% 0.47/0.63    (![A:$i,B:$i,C:$i]:
% 0.47/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.47/0.63         ( ~( v1_xboole_0 @ B ) ) & 
% 0.47/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.47/0.63         ( ~( v1_xboole_0 @ C ) ) & 
% 0.47/0.63         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.47/0.63         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.47/0.63         ( m1_subset_1 @
% 0.47/0.63           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.47/0.63       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.47/0.63         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.47/0.63         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.47/0.63         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.47/0.63  thf('9', plain,
% 0.47/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.47/0.63          | (v1_xboole_0 @ X7)
% 0.47/0.63          | ~ (l1_struct_0 @ X8)
% 0.47/0.63          | (v2_struct_0 @ X8)
% 0.47/0.63          | (v1_xboole_0 @ X9)
% 0.47/0.63          | ~ (v2_waybel_0 @ X9 @ (k3_yellow_1 @ X7))
% 0.47/0.63          | ~ (v13_waybel_0 @ X9 @ (k3_yellow_1 @ X7))
% 0.47/0.63          | ~ (m1_subset_1 @ X9 @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X7))))
% 0.47/0.63          | (v4_orders_2 @ (k3_yellow19 @ X8 @ X7 @ X9)))),
% 0.47/0.63      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.47/0.63  thf('10', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.47/0.63          | ~ (v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.63  thf('11', plain,
% 0.47/0.63      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('12', plain,
% 0.47/0.63      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('13', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.47/0.63  thf('14', plain,
% 0.47/0.63      ((~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['7', '13'])).
% 0.47/0.63  thf('15', plain,
% 0.47/0.63      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.63      inference('simplify', [status(thm)], ['14'])).
% 0.47/0.63  thf('16', plain,
% 0.47/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['6', '15'])).
% 0.47/0.63  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('18', plain,
% 0.47/0.63      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('demod', [status(thm)], ['16', '17'])).
% 0.47/0.63  thf('19', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('20', plain,
% 0.47/0.63      (![X1 : $i]:
% 0.47/0.63         ((m1_subset_1 @ (k2_struct_0 @ X1) @ 
% 0.47/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.47/0.63          | ~ (l1_struct_0 @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.47/0.63  thf('21', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B @ 
% 0.47/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(fc5_yellow19, axiom,
% 0.47/0.63    (![A:$i,B:$i,C:$i]:
% 0.47/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.47/0.63         ( ~( v1_xboole_0 @ B ) ) & 
% 0.47/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.47/0.63         ( ~( v1_xboole_0 @ C ) ) & 
% 0.47/0.63         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.47/0.63         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.47/0.63         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.47/0.63         ( m1_subset_1 @
% 0.47/0.63           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.47/0.63       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.47/0.63         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.47/0.63         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.47/0.63  thf('22', plain,
% 0.47/0.63      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.47/0.63          | (v1_xboole_0 @ X10)
% 0.47/0.63          | ~ (l1_struct_0 @ X11)
% 0.47/0.63          | (v2_struct_0 @ X11)
% 0.47/0.63          | (v1_xboole_0 @ X12)
% 0.47/0.63          | ~ (v1_subset_1 @ X12 @ (u1_struct_0 @ (k3_yellow_1 @ X10)))
% 0.47/0.63          | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.47/0.63          | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.47/0.63          | ~ (m1_subset_1 @ X12 @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X10))))
% 0.47/0.63          | (v7_waybel_0 @ (k3_yellow19 @ X11 @ X10 @ X12)))),
% 0.47/0.63      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.47/0.63  thf('23', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.47/0.63          | ~ (v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.47/0.63          | ~ (v1_subset_1 @ sk_B @ 
% 0.47/0.63               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.47/0.63  thf('24', plain,
% 0.47/0.63      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('25', plain,
% 0.47/0.63      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('26', plain,
% 0.47/0.63      ((v1_subset_1 @ sk_B @ 
% 0.47/0.63        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('27', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.47/0.63  thf('28', plain,
% 0.47/0.63      ((~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['20', '27'])).
% 0.47/0.63  thf('29', plain,
% 0.47/0.63      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.63      inference('simplify', [status(thm)], ['28'])).
% 0.47/0.63  thf('30', plain,
% 0.47/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['19', '29'])).
% 0.47/0.63  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('32', plain,
% 0.47/0.63      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('demod', [status(thm)], ['30', '31'])).
% 0.47/0.63  thf('33', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('34', plain,
% 0.47/0.63      (![X1 : $i]:
% 0.47/0.63         ((m1_subset_1 @ (k2_struct_0 @ X1) @ 
% 0.47/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.47/0.63          | ~ (l1_struct_0 @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.47/0.63  thf('35', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B @ 
% 0.47/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(dt_k3_yellow19, axiom,
% 0.47/0.63    (![A:$i,B:$i,C:$i]:
% 0.47/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.47/0.63         ( ~( v1_xboole_0 @ B ) ) & 
% 0.47/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.47/0.63         ( ~( v1_xboole_0 @ C ) ) & 
% 0.47/0.63         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.47/0.63         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.47/0.63         ( m1_subset_1 @
% 0.47/0.63           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.47/0.63       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.47/0.63         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.47/0.63         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.47/0.63  thf('36', plain,
% 0.47/0.63      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.47/0.63          | (v1_xboole_0 @ X4)
% 0.47/0.63          | ~ (l1_struct_0 @ X5)
% 0.47/0.63          | (v2_struct_0 @ X5)
% 0.47/0.63          | (v1_xboole_0 @ X6)
% 0.47/0.63          | ~ (v2_waybel_0 @ X6 @ (k3_yellow_1 @ X4))
% 0.47/0.63          | ~ (v13_waybel_0 @ X6 @ (k3_yellow_1 @ X4))
% 0.47/0.63          | ~ (m1_subset_1 @ X6 @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X4))))
% 0.47/0.63          | (l1_waybel_0 @ (k3_yellow19 @ X5 @ X4 @ X6) @ X5))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.47/0.63  thf('37', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.47/0.63          | ~ (v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.47/0.63          | ~ (v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.47/0.63  thf('38', plain,
% 0.47/0.63      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('39', plain,
% 0.47/0.63      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('40', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.47/0.63  thf('41', plain,
% 0.47/0.63      ((~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.47/0.63           sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['34', '40'])).
% 0.47/0.63  thf('42', plain,
% 0.47/0.63      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.47/0.63         sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.63      inference('simplify', [status(thm)], ['41'])).
% 0.47/0.63  thf('43', plain,
% 0.47/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.47/0.63           sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['33', '42'])).
% 0.47/0.63  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('45', plain,
% 0.47/0.63      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.47/0.63           sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['43', '44'])).
% 0.47/0.63  thf('46', plain,
% 0.47/0.63      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.47/0.63        | (r2_hidden @ sk_C @ 
% 0.47/0.63           (k10_yellow_6 @ sk_A @ 
% 0.47/0.63            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('47', plain,
% 0.47/0.63      (((r2_hidden @ sk_C @ 
% 0.47/0.63         (k10_yellow_6 @ sk_A @ 
% 0.47/0.63          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.47/0.63         <= (((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('split', [status(esa)], ['46'])).
% 0.47/0.63  thf(t13_yellow19, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.47/0.63             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.47/0.63           ( ![C:$i]:
% 0.47/0.63             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.63               ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) <=>
% 0.47/0.63                 ( r2_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.47/0.63  thf('48', plain,
% 0.47/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.47/0.63         ((v2_struct_0 @ X13)
% 0.47/0.63          | ~ (v4_orders_2 @ X13)
% 0.47/0.63          | ~ (v7_waybel_0 @ X13)
% 0.47/0.63          | ~ (l1_waybel_0 @ X13 @ X14)
% 0.47/0.63          | ~ (r2_hidden @ X15 @ (k10_yellow_6 @ X14 @ X13))
% 0.47/0.63          | (r2_waybel_7 @ X14 @ (k2_yellow19 @ X14 @ X13) @ X15)
% 0.47/0.63          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.47/0.63          | ~ (l1_pre_topc @ X14)
% 0.47/0.63          | ~ (v2_pre_topc @ X14)
% 0.47/0.63          | (v2_struct_0 @ X14))),
% 0.47/0.63      inference('cnf', [status(esa)], [t13_yellow19])).
% 0.47/0.63  thf('49', plain,
% 0.47/0.63      ((((v2_struct_0 @ sk_A)
% 0.47/0.63         | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63         | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | (r2_waybel_7 @ sk_A @ 
% 0.47/0.63            (k2_yellow19 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.47/0.63            sk_C)
% 0.47/0.63         | ~ (l1_waybel_0 @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.47/0.63         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.47/0.63         <= (((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['47', '48'])).
% 0.47/0.63  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('52', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('53', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('54', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B @ 
% 0.47/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(t15_yellow19, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.47/0.63             ( v1_subset_1 @
% 0.47/0.63               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.47/0.63             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.47/0.63             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.47/0.63             ( m1_subset_1 @
% 0.47/0.63               B @ 
% 0.47/0.63               ( k1_zfmisc_1 @
% 0.47/0.63                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.47/0.63           ( ( B ) =
% 0.47/0.63             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.47/0.63  thf('55', plain,
% 0.47/0.63      (![X16 : $i, X17 : $i]:
% 0.47/0.63         ((v1_xboole_0 @ X16)
% 0.47/0.63          | ~ (v1_subset_1 @ X16 @ 
% 0.47/0.63               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X17))))
% 0.47/0.63          | ~ (v2_waybel_0 @ X16 @ (k3_yellow_1 @ (k2_struct_0 @ X17)))
% 0.47/0.63          | ~ (v13_waybel_0 @ X16 @ (k3_yellow_1 @ (k2_struct_0 @ X17)))
% 0.47/0.63          | ~ (m1_subset_1 @ X16 @ 
% 0.47/0.63               (k1_zfmisc_1 @ 
% 0.47/0.63                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X17)))))
% 0.47/0.63          | ((X16)
% 0.47/0.63              = (k2_yellow19 @ X17 @ 
% 0.47/0.63                 (k3_yellow19 @ X17 @ (k2_struct_0 @ X17) @ X16)))
% 0.47/0.63          | ~ (l1_struct_0 @ X17)
% 0.47/0.63          | (v2_struct_0 @ X17))),
% 0.47/0.63      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.47/0.63  thf('56', plain,
% 0.47/0.63      (((v2_struct_0 @ sk_A)
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | ((sk_B)
% 0.47/0.63            = (k2_yellow19 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.47/0.63        | ~ (v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.47/0.63        | ~ (v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.47/0.63        | ~ (v1_subset_1 @ sk_B @ 
% 0.47/0.63             (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63        | (v1_xboole_0 @ sk_B))),
% 0.47/0.63      inference('sup-', [status(thm)], ['54', '55'])).
% 0.47/0.63  thf('57', plain,
% 0.47/0.63      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('58', plain,
% 0.47/0.63      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('59', plain,
% 0.47/0.63      ((v1_subset_1 @ sk_B @ 
% 0.47/0.63        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('60', plain,
% 0.47/0.63      (((v2_struct_0 @ sk_A)
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | ((sk_B)
% 0.47/0.63            = (k2_yellow19 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.47/0.63        | (v1_xboole_0 @ sk_B))),
% 0.47/0.63      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.47/0.63  thf('61', plain,
% 0.47/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | ((sk_B)
% 0.47/0.63            = (k2_yellow19 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.47/0.63        | (v2_struct_0 @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['53', '60'])).
% 0.47/0.63  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('63', plain,
% 0.47/0.63      (((v1_xboole_0 @ sk_B)
% 0.47/0.63        | ((sk_B)
% 0.47/0.63            = (k2_yellow19 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.47/0.63        | (v2_struct_0 @ sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['61', '62'])).
% 0.47/0.63  thf('64', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('65', plain,
% 0.47/0.63      (((v2_struct_0 @ sk_A)
% 0.47/0.63        | ((sk_B)
% 0.47/0.63            = (k2_yellow19 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.47/0.63      inference('clc', [status(thm)], ['63', '64'])).
% 0.47/0.63  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('67', plain,
% 0.47/0.63      (((sk_B)
% 0.47/0.63         = (k2_yellow19 @ sk_A @ 
% 0.47/0.63            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('clc', [status(thm)], ['65', '66'])).
% 0.47/0.63  thf('68', plain,
% 0.47/0.63      ((((v2_struct_0 @ sk_A)
% 0.47/0.63         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.47/0.63         | ~ (l1_waybel_0 @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.47/0.63         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.47/0.63         <= (((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('demod', [status(thm)], ['49', '50', '51', '52', '67'])).
% 0.47/0.63  thf('69', plain,
% 0.47/0.63      ((((v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.47/0.63         | (v2_struct_0 @ sk_A)))
% 0.47/0.63         <= (((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['45', '68'])).
% 0.47/0.63  thf('70', plain,
% 0.47/0.63      ((((r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.47/0.63         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)))
% 0.47/0.63         <= (((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('simplify', [status(thm)], ['69'])).
% 0.47/0.63  thf('71', plain,
% 0.47/0.63      ((((v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | (v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.47/0.63         <= (((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['32', '70'])).
% 0.47/0.63  thf('72', plain,
% 0.47/0.63      ((((r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.47/0.63         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)))
% 0.47/0.63         <= (((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('simplify', [status(thm)], ['71'])).
% 0.47/0.63  thf('73', plain,
% 0.47/0.63      ((((v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | (v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.47/0.63         <= (((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['18', '72'])).
% 0.47/0.63  thf('74', plain,
% 0.47/0.63      ((((r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.47/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)))
% 0.47/0.63         <= (((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('simplify', [status(thm)], ['73'])).
% 0.47/0.63  thf('75', plain,
% 0.47/0.63      (![X1 : $i]:
% 0.47/0.63         ((m1_subset_1 @ (k2_struct_0 @ X1) @ 
% 0.47/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.47/0.63          | ~ (l1_struct_0 @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.47/0.63  thf('76', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B @ 
% 0.47/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('77', plain,
% 0.47/0.63      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.47/0.63          | (v1_xboole_0 @ X4)
% 0.47/0.63          | ~ (l1_struct_0 @ X5)
% 0.47/0.63          | (v2_struct_0 @ X5)
% 0.47/0.63          | (v1_xboole_0 @ X6)
% 0.47/0.63          | ~ (v2_waybel_0 @ X6 @ (k3_yellow_1 @ X4))
% 0.47/0.63          | ~ (v13_waybel_0 @ X6 @ (k3_yellow_1 @ X4))
% 0.47/0.63          | ~ (m1_subset_1 @ X6 @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X4))))
% 0.47/0.63          | ~ (v2_struct_0 @ (k3_yellow19 @ X5 @ X4 @ X6)))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.47/0.63  thf('78', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.47/0.63          | ~ (v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['76', '77'])).
% 0.47/0.63  thf('79', plain,
% 0.47/0.63      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('80', plain,
% 0.47/0.63      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('81', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.47/0.63  thf('82', plain,
% 0.47/0.63      ((~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['75', '81'])).
% 0.47/0.63  thf('83', plain,
% 0.47/0.63      ((~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.63      inference('simplify', [status(thm)], ['82'])).
% 0.47/0.63  thf('84', plain,
% 0.47/0.63      ((((v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.47/0.63         | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)))
% 0.47/0.63         <= (((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['74', '83'])).
% 0.47/0.63  thf('85', plain,
% 0.47/0.63      (((~ (l1_struct_0 @ sk_A)
% 0.47/0.63         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)))
% 0.47/0.63         <= (((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('simplify', [status(thm)], ['84'])).
% 0.47/0.63  thf('86', plain,
% 0.47/0.63      (((~ (l1_pre_topc @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.47/0.63         <= (((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['5', '85'])).
% 0.47/0.63  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('88', plain,
% 0.47/0.63      ((((v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C)))
% 0.47/0.63         <= (((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('demod', [status(thm)], ['86', '87'])).
% 0.47/0.63  thf('89', plain,
% 0.47/0.63      ((~ (r2_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.47/0.63         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('split', [status(esa)], ['0'])).
% 0.47/0.63  thf('90', plain,
% 0.47/0.63      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)))
% 0.47/0.63         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['88', '89'])).
% 0.47/0.63  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('92', plain,
% 0.47/0.63      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('clc', [status(thm)], ['90', '91'])).
% 0.47/0.63  thf('93', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('94', plain,
% 0.47/0.63      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.47/0.63         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('clc', [status(thm)], ['92', '93'])).
% 0.47/0.63  thf('95', plain,
% 0.47/0.63      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.47/0.63         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('sup+', [status(thm)], ['4', '94'])).
% 0.47/0.63  thf('96', plain,
% 0.47/0.63      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['3', '95'])).
% 0.47/0.63  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('98', plain,
% 0.47/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.47/0.63         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('demod', [status(thm)], ['96', '97'])).
% 0.47/0.63  thf(fc2_struct_0, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.47/0.63       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.47/0.63  thf('99', plain,
% 0.47/0.63      (![X3 : $i]:
% 0.47/0.63         (~ (v1_xboole_0 @ (u1_struct_0 @ X3))
% 0.47/0.63          | ~ (l1_struct_0 @ X3)
% 0.47/0.63          | (v2_struct_0 @ X3))),
% 0.47/0.63      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.47/0.63  thf('100', plain,
% 0.47/0.63      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.47/0.63         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['98', '99'])).
% 0.47/0.63  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('102', plain,
% 0.47/0.63      ((~ (l1_struct_0 @ sk_A))
% 0.47/0.63         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('clc', [status(thm)], ['100', '101'])).
% 0.47/0.63  thf('103', plain,
% 0.47/0.63      ((~ (l1_pre_topc @ sk_A))
% 0.47/0.63         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) & 
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['2', '102'])).
% 0.47/0.63  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('105', plain,
% 0.47/0.63      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.47/0.63       ~
% 0.47/0.63       ((r2_hidden @ sk_C @ 
% 0.47/0.63         (k10_yellow_6 @ sk_A @ 
% 0.47/0.63          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.47/0.63      inference('demod', [status(thm)], ['103', '104'])).
% 0.47/0.63  thf('106', plain,
% 0.47/0.63      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.47/0.63       ((r2_hidden @ sk_C @ 
% 0.47/0.63         (k10_yellow_6 @ sk_A @ 
% 0.47/0.63          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.47/0.63      inference('split', [status(esa)], ['46'])).
% 0.47/0.63  thf('107', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('108', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('109', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.63  thf('110', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('111', plain,
% 0.47/0.63      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C))
% 0.47/0.63         <= (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('split', [status(esa)], ['46'])).
% 0.47/0.63  thf('112', plain,
% 0.47/0.63      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('demod', [status(thm)], ['16', '17'])).
% 0.47/0.63  thf('113', plain,
% 0.47/0.63      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('demod', [status(thm)], ['30', '31'])).
% 0.47/0.63  thf('114', plain,
% 0.47/0.63      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.47/0.63           sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['43', '44'])).
% 0.47/0.63  thf('115', plain,
% 0.47/0.63      (((sk_B)
% 0.47/0.63         = (k2_yellow19 @ sk_A @ 
% 0.47/0.63            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('clc', [status(thm)], ['65', '66'])).
% 0.47/0.63  thf('116', plain,
% 0.47/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.47/0.63         ((v2_struct_0 @ X13)
% 0.47/0.63          | ~ (v4_orders_2 @ X13)
% 0.47/0.63          | ~ (v7_waybel_0 @ X13)
% 0.47/0.63          | ~ (l1_waybel_0 @ X13 @ X14)
% 0.47/0.63          | ~ (r2_waybel_7 @ X14 @ (k2_yellow19 @ X14 @ X13) @ X15)
% 0.47/0.63          | (r2_hidden @ X15 @ (k10_yellow_6 @ X14 @ X13))
% 0.47/0.63          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.47/0.63          | ~ (l1_pre_topc @ X14)
% 0.47/0.63          | ~ (v2_pre_topc @ X14)
% 0.47/0.63          | (v2_struct_0 @ X14))),
% 0.47/0.63      inference('cnf', [status(esa)], [t13_yellow19])).
% 0.47/0.63  thf('117', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.47/0.63          | ~ (l1_waybel_0 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.47/0.63          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['115', '116'])).
% 0.47/0.63  thf('118', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('120', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.47/0.63          | ~ (l1_waybel_0 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.47/0.63          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.47/0.63      inference('demod', [status(thm)], ['117', '118', '119'])).
% 0.47/0.63  thf('121', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['114', '120'])).
% 0.47/0.63  thf('122', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.47/0.63          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B))),
% 0.47/0.63      inference('simplify', [status(thm)], ['121'])).
% 0.47/0.63  thf('123', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['113', '122'])).
% 0.47/0.63  thf('124', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.47/0.63          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B))),
% 0.47/0.63      inference('simplify', [status(thm)], ['123'])).
% 0.47/0.63  thf('125', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | (v1_xboole_0 @ sk_B)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['112', '124'])).
% 0.47/0.63  thf('126', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B))),
% 0.47/0.63      inference('simplify', [status(thm)], ['125'])).
% 0.47/0.63  thf('127', plain,
% 0.47/0.63      ((((v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | (r2_hidden @ sk_C @ 
% 0.47/0.63            (k10_yellow_6 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.47/0.63         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))))
% 0.47/0.63         <= (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['111', '126'])).
% 0.47/0.63  thf('128', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('129', plain,
% 0.47/0.63      ((((v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | (r2_hidden @ sk_C @ 
% 0.47/0.63            (k10_yellow_6 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 0.47/0.63         <= (((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('demod', [status(thm)], ['127', '128'])).
% 0.47/0.63  thf('130', plain,
% 0.47/0.63      ((~ (r2_hidden @ sk_C @ 
% 0.47/0.63           (k10_yellow_6 @ sk_A @ 
% 0.47/0.63            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.47/0.63      inference('split', [status(esa)], ['0'])).
% 0.47/0.63  thf('131', plain,
% 0.47/0.63      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.47/0.63             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['129', '130'])).
% 0.47/0.63  thf('132', plain,
% 0.47/0.63      ((~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.47/0.63        | (v1_xboole_0 @ sk_B)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.63      inference('simplify', [status(thm)], ['82'])).
% 0.47/0.63  thf('133', plain,
% 0.47/0.63      ((((v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.47/0.63             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['131', '132'])).
% 0.47/0.63  thf('134', plain,
% 0.47/0.63      (((~ (l1_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.47/0.63             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('simplify', [status(thm)], ['133'])).
% 0.47/0.63  thf('135', plain,
% 0.47/0.63      (((~ (l1_pre_topc @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.47/0.63             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['110', '134'])).
% 0.47/0.63  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('137', plain,
% 0.47/0.63      ((((v1_xboole_0 @ sk_B)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.47/0.63             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('demod', [status(thm)], ['135', '136'])).
% 0.47/0.63  thf('138', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('139', plain,
% 0.47/0.63      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.47/0.63             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('clc', [status(thm)], ['137', '138'])).
% 0.47/0.63  thf('140', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('141', plain,
% 0.47/0.63      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.47/0.63             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('clc', [status(thm)], ['139', '140'])).
% 0.47/0.63  thf('142', plain,
% 0.47/0.63      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.47/0.63             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('sup+', [status(thm)], ['109', '141'])).
% 0.47/0.63  thf('143', plain,
% 0.47/0.63      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.47/0.63             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['108', '142'])).
% 0.47/0.63  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('145', plain,
% 0.47/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.47/0.63             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('demod', [status(thm)], ['143', '144'])).
% 0.47/0.63  thf('146', plain,
% 0.47/0.63      (![X3 : $i]:
% 0.47/0.63         (~ (v1_xboole_0 @ (u1_struct_0 @ X3))
% 0.47/0.63          | ~ (l1_struct_0 @ X3)
% 0.47/0.63          | (v2_struct_0 @ X3))),
% 0.47/0.63      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.47/0.63  thf('147', plain,
% 0.47/0.63      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.47/0.63             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['145', '146'])).
% 0.47/0.63  thf('148', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('149', plain,
% 0.47/0.63      ((~ (l1_struct_0 @ sk_A))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.47/0.63             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('clc', [status(thm)], ['147', '148'])).
% 0.47/0.63  thf('150', plain,
% 0.47/0.63      ((~ (l1_pre_topc @ sk_A))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.47/0.63             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['107', '149'])).
% 0.47/0.63  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('152', plain,
% 0.47/0.63      (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C)) | 
% 0.47/0.63       ((r2_hidden @ sk_C @ 
% 0.47/0.63         (k10_yellow_6 @ sk_A @ 
% 0.47/0.63          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.47/0.63      inference('demod', [status(thm)], ['150', '151'])).
% 0.47/0.63  thf('153', plain, ($false),
% 0.47/0.63      inference('sat_resolution*', [status(thm)], ['1', '105', '106', '152'])).
% 0.47/0.63  
% 0.47/0.63  % SZS output end Refutation
% 0.47/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
