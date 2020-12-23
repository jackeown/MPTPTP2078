%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LxNTY4nLzb

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:54 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  326 (1289 expanded)
%              Number of leaves         :   41 ( 417 expanded)
%              Depth                    :   63
%              Number of atoms          : 4190 (23382 expanded)
%              Number of equality atoms :   50 ( 349 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6 = X5 )
      | ( v1_subset_1 @ X6 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('14',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('15',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('16',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
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

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v2_waybel_0 @ X12 @ ( k3_yellow_1 @ X10 ) )
      | ~ ( v13_waybel_0 @ X12 @ ( k3_yellow_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X10 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('18',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('19',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('20',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v2_waybel_0 @ X12 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) )
      | ~ ( v13_waybel_0 @ X12 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X11 @ X10 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('25',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('28',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['22','25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','33'])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('40',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('41',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
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

thf('43',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v1_subset_1 @ X15 @ ( u1_struct_0 @ ( k3_yellow_1 @ X13 ) ) )
      | ~ ( v2_waybel_0 @ X15 @ ( k3_yellow_1 @ X13 ) )
      | ~ ( v13_waybel_0 @ X15 @ ( k3_yellow_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X13 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('44',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('45',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('46',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('47',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('48',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v1_subset_1 @ X15 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) )
      | ~ ( v2_waybel_0 @ X15 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) )
      | ~ ( v13_waybel_0 @ X15 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X14 @ X13 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('51',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('52',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('54',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['41','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','59'])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('65',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('66',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('67',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
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

thf('69',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v2_waybel_0 @ X9 @ ( k3_yellow_1 @ X7 ) )
      | ~ ( v13_waybel_0 @ X9 @ ( k3_yellow_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X7 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X8 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('70',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('71',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('72',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('73',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v2_waybel_0 @ X9 @ ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) )
      | ~ ( v13_waybel_0 @ X9 @ ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X8 @ X7 @ X9 ) @ X8 ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('76',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['65','81'])).

thf('83',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['86'])).

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

thf('88',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( r2_hidden @ X18 @ ( k10_yellow_6 @ X17 @ X16 ) )
      | ( r2_waybel_7 @ X17 @ ( k2_yellow19 @ X17 @ X16 ) @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow19])).

thf('89',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r2_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_C )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('94',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
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

thf('95',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( v1_subset_1 @ X19 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X20 ) ) ) )
      | ~ ( v2_waybel_0 @ X19 @ ( k3_yellow_1 @ ( k2_struct_0 @ X20 ) ) )
      | ~ ( v13_waybel_0 @ X19 @ ( k3_yellow_1 @ ( k2_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X20 ) ) ) ) )
      | ( X19
        = ( k2_yellow19 @ X20 @ ( k3_yellow19 @ X20 @ ( k2_struct_0 @ X20 ) @ X19 ) ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('96',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('97',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('98',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('99',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('100',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( v1_subset_1 @ X19 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X20 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X19 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X20 ) ) ) )
      | ~ ( v13_waybel_0 @ X19 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X20 ) ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X20 ) ) ) ) ) )
      | ( X19
        = ( k2_yellow19 @ X20 @ ( k3_yellow19 @ X20 @ ( k2_struct_0 @ X20 ) @ X19 ) ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['94','100'])).

thf('102',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('103',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('104',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['101','102','103','104'])).

thf('106',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['93','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( sk_B_1
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','112'])).

thf('114',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['114'])).

thf('116',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('117',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('118',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('119',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('120',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
   <= ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['86'])).

thf('121',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('122',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('123',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('124',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('125',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('126',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('127',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v1_subset_1 @ X15 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) )
      | ~ ( v2_waybel_0 @ X15 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) )
      | ~ ( v13_waybel_0 @ X15 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X14 @ X13 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('134',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('135',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('136',plain,
    ( ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['133','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('141',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('142',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('143',plain,
    ( ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['140','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('148',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('149',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('150',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['147','150'])).

thf('152',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['132','139','146','153'])).

thf('155',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['123','154'])).

thf('156',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','155'])).

thf('157',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('160',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('161',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('162',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v2_waybel_0 @ X12 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) )
      | ~ ( v13_waybel_0 @ X12 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X11 @ X10 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('165',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['160','166'])).

thf('168',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['159','167'])).

thf('169',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('172',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('173',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('174',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('175',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('176',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v2_waybel_0 @ X9 @ ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) )
      | ~ ( v13_waybel_0 @ X9 @ ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X8 @ X7 @ X9 ) @ X8 ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('179',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('181',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['174','180'])).

thf('182',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['173','181'])).

thf('183',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('186',plain,
    ( sk_B_1
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('187',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( r2_waybel_7 @ X17 @ ( k2_yellow19 @ X17 @ X16 ) @ X18 )
      | ( r2_hidden @ X18 @ ( k10_yellow_6 @ X17 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow19])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['185','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['184','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['172','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['171','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['170','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['158','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['121','202'])).

thf('204',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','205'])).

thf('207',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['114'])).

thf('210',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('212',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('213',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('214',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('215',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v2_waybel_0 @ X9 @ ( k3_yellow_1 @ X7 ) )
      | ~ ( v13_waybel_0 @ X9 @ ( k3_yellow_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X7 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X8 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('216',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('217',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('218',plain,(
    ! [X4: $i] :
      ( ( k3_yellow_1 @ X4 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('219',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v2_waybel_0 @ X9 @ ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) )
      | ~ ( v13_waybel_0 @ X9 @ ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X7 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X8 @ X7 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['215','216','217','218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['214','219'])).

thf('221',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('222',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['213','223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['212','224'])).

thf('226',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['211','227'])).

thf('229',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['210','228'])).

thf('230',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['119','230'])).

thf('232',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('234',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['118','233'])).

thf('235',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['117','235'])).

thf('237',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['236','237'])).

thf('239',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['238','239'])).

thf('241',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['240','241'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('243',plain,(
    ! [X3: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('244',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['244','245'])).

thf('247',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['116','246'])).

thf('248',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['247','248'])).

thf('250',plain,
    ( ( r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['86'])).

thf('251',plain,(
    r2_hidden @ sk_C @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['115','249','250'])).

thf('252',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['113','251'])).

thf('253',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','252'])).

thf('254',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['253'])).

thf('255',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','254'])).

thf('256',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['255'])).

thf('257',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','256'])).

thf('258',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['211','227'])).

thf('260',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['260'])).

thf('262',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','261'])).

thf('263',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['262','263'])).

thf('265',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C )
   <= ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['114'])).

thf('266',plain,(
    ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['115','249'])).

thf('267',plain,(
    ~ ( r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['265','266'])).

thf('268',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['264','267'])).

thf('269',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['268','269'])).

thf('271',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['270','271'])).

thf('273',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','272'])).

thf('274',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','273'])).

thf('275',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['274','275'])).

thf('277',plain,(
    ! [X3: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('278',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['276','277'])).

thf('279',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    ~ ( l1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['278','279'])).

thf('281',plain,(
    ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','280'])).

thf('282',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    $false ),
    inference(demod,[status(thm)],['281','282'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LxNTY4nLzb
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:15:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.63  % Solved by: fo/fo7.sh
% 0.47/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.63  % done 165 iterations in 0.152s
% 0.47/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.63  % SZS output start Refutation
% 0.47/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.63  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.63  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.47/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.63  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.47/0.63  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.47/0.63  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.47/0.63  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.47/0.63  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.47/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.63  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.47/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.63  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.47/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.47/0.63  thf(r2_waybel_7_type, type, r2_waybel_7: $i > $i > $i > $o).
% 0.47/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.63  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.47/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.63  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.47/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.63  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.47/0.63  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.47/0.63  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.47/0.63  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.47/0.63  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.47/0.63  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.47/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.47/0.63  thf(dt_l1_pre_topc, axiom,
% 0.47/0.63    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.47/0.63  thf('0', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('1', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf(d3_struct_0, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.47/0.63  thf('2', plain,
% 0.47/0.63      (![X1 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.63  thf('3', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('4', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf(rc3_subset_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ?[B:$i]:
% 0.47/0.63       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.47/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.47/0.63  thf('5', plain,
% 0.47/0.63      (![X0 : $i]: (m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.47/0.63      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.47/0.63  thf('6', plain,
% 0.47/0.63      (![X0 : $i]: (m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.47/0.63      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.47/0.63  thf(d7_subset_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.63       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.47/0.63  thf('7', plain,
% 0.47/0.63      (![X5 : $i, X6 : $i]:
% 0.47/0.63         (((X6) = (X5))
% 0.47/0.63          | (v1_subset_1 @ X6 @ X5)
% 0.47/0.63          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.47/0.63  thf('8', plain,
% 0.47/0.63      (![X0 : $i]: ((v1_subset_1 @ (sk_B @ X0) @ X0) | ((sk_B @ X0) = (X0)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.63  thf('9', plain, (![X0 : $i]: ~ (v1_subset_1 @ (sk_B @ X0) @ X0)),
% 0.47/0.63      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.47/0.63  thf('10', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 0.47/0.63      inference('clc', [status(thm)], ['8', '9'])).
% 0.47/0.63  thf('11', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.63      inference('demod', [status(thm)], ['5', '10'])).
% 0.47/0.63  thf('12', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('13', plain,
% 0.47/0.63      (![X1 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.63  thf(t18_yellow19, conjecture,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
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
% 0.47/0.63           ( ![C:$i]:
% 0.47/0.63             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.63               ( ( r2_hidden @
% 0.47/0.63                   C @ 
% 0.47/0.63                   ( k10_yellow_6 @
% 0.47/0.63                     A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) <=>
% 0.47/0.63                 ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.47/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.63    (~( ![A:$i]:
% 0.47/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.63            ( l1_pre_topc @ A ) ) =>
% 0.47/0.63          ( ![B:$i]:
% 0.47/0.63            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.47/0.63                ( v1_subset_1 @
% 0.47/0.63                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.47/0.63                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.47/0.63                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.47/0.63                ( m1_subset_1 @
% 0.47/0.63                  B @ 
% 0.47/0.63                  ( k1_zfmisc_1 @
% 0.47/0.63                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.47/0.63              ( ![C:$i]:
% 0.47/0.63                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.63                  ( ( r2_hidden @
% 0.47/0.63                      C @ 
% 0.47/0.63                      ( k10_yellow_6 @
% 0.47/0.63                        A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) <=>
% 0.47/0.63                    ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.47/0.63    inference('cnf.neg', [status(esa)], [t18_yellow19])).
% 0.47/0.63  thf('14', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B_1 @ 
% 0.47/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(d2_yellow_1, axiom,
% 0.47/0.63    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.47/0.63  thf('15', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('16', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B_1 @ 
% 0.47/0.63        (k1_zfmisc_1 @ 
% 0.47/0.63         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.47/0.63      inference('demod', [status(thm)], ['14', '15'])).
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
% 0.47/0.63  thf('17', plain,
% 0.47/0.63      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.47/0.63          | (v1_xboole_0 @ X10)
% 0.47/0.63          | ~ (l1_struct_0 @ X11)
% 0.47/0.63          | (v2_struct_0 @ X11)
% 0.47/0.63          | (v1_xboole_0 @ X12)
% 0.47/0.63          | ~ (v2_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.47/0.63          | ~ (v13_waybel_0 @ X12 @ (k3_yellow_1 @ X10))
% 0.47/0.63          | ~ (m1_subset_1 @ X12 @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X10))))
% 0.47/0.63          | (v4_orders_2 @ (k3_yellow19 @ X11 @ X10 @ X12)))),
% 0.47/0.63      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.47/0.63  thf('18', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('19', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('20', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('21', plain,
% 0.47/0.63      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.47/0.63          | (v1_xboole_0 @ X10)
% 0.47/0.63          | ~ (l1_struct_0 @ X11)
% 0.47/0.63          | (v2_struct_0 @ X11)
% 0.47/0.63          | (v1_xboole_0 @ X12)
% 0.47/0.63          | ~ (v2_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.47/0.63          | ~ (v13_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.47/0.63          | ~ (m1_subset_1 @ X12 @ 
% 0.47/0.63               (k1_zfmisc_1 @ 
% 0.47/0.63                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X10)))))
% 0.47/0.63          | (v4_orders_2 @ (k3_yellow19 @ X11 @ X10 @ X12)))),
% 0.47/0.63      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.47/0.63  thf('22', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['16', '21'])).
% 0.47/0.63  thf('23', plain,
% 0.47/0.63      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('24', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('25', plain,
% 0.47/0.63      ((v13_waybel_0 @ sk_B_1 @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['23', '24'])).
% 0.47/0.63  thf('26', plain,
% 0.47/0.63      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('27', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('28', plain,
% 0.47/0.63      ((v2_waybel_0 @ sk_B_1 @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['26', '27'])).
% 0.47/0.63  thf('29', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['22', '25', '28'])).
% 0.47/0.63  thf('30', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['13', '29'])).
% 0.47/0.63  thf('31', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ sk_A)
% 0.47/0.63          | (v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['12', '30'])).
% 0.47/0.63  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('33', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['31', '32'])).
% 0.47/0.63  thf('34', plain,
% 0.47/0.63      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['11', '33'])).
% 0.47/0.63  thf('35', plain,
% 0.47/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['4', '34'])).
% 0.47/0.63  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('37', plain,
% 0.47/0.63      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['35', '36'])).
% 0.47/0.63  thf('38', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('39', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.63      inference('demod', [status(thm)], ['5', '10'])).
% 0.47/0.63  thf('40', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('41', plain,
% 0.47/0.63      (![X1 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.63  thf('42', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B_1 @ 
% 0.47/0.63        (k1_zfmisc_1 @ 
% 0.47/0.63         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.47/0.63      inference('demod', [status(thm)], ['14', '15'])).
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
% 0.47/0.63  thf('43', plain,
% 0.47/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.47/0.63          | (v1_xboole_0 @ X13)
% 0.47/0.63          | ~ (l1_struct_0 @ X14)
% 0.47/0.63          | (v2_struct_0 @ X14)
% 0.47/0.63          | (v1_xboole_0 @ X15)
% 0.47/0.63          | ~ (v1_subset_1 @ X15 @ (u1_struct_0 @ (k3_yellow_1 @ X13)))
% 0.47/0.63          | ~ (v2_waybel_0 @ X15 @ (k3_yellow_1 @ X13))
% 0.47/0.63          | ~ (v13_waybel_0 @ X15 @ (k3_yellow_1 @ X13))
% 0.47/0.63          | ~ (m1_subset_1 @ X15 @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X13))))
% 0.47/0.63          | (v7_waybel_0 @ (k3_yellow19 @ X14 @ X13 @ X15)))),
% 0.47/0.63      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.47/0.63  thf('44', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('45', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('46', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('47', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('48', plain,
% 0.47/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.47/0.63          | (v1_xboole_0 @ X13)
% 0.47/0.63          | ~ (l1_struct_0 @ X14)
% 0.47/0.63          | (v2_struct_0 @ X14)
% 0.47/0.63          | (v1_xboole_0 @ X15)
% 0.47/0.63          | ~ (v1_subset_1 @ X15 @ 
% 0.47/0.63               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X13))))
% 0.47/0.63          | ~ (v2_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.47/0.63          | ~ (v13_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.47/0.63          | ~ (m1_subset_1 @ X15 @ 
% 0.47/0.63               (k1_zfmisc_1 @ 
% 0.47/0.63                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X13)))))
% 0.47/0.63          | (v7_waybel_0 @ (k3_yellow19 @ X14 @ X13 @ X15)))),
% 0.47/0.63      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.47/0.63  thf('49', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63          | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.47/0.63               (u1_struct_0 @ 
% 0.47/0.63                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['42', '48'])).
% 0.47/0.63  thf('50', plain,
% 0.47/0.63      ((v13_waybel_0 @ sk_B_1 @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['23', '24'])).
% 0.47/0.63  thf('51', plain,
% 0.47/0.63      ((v2_waybel_0 @ sk_B_1 @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['26', '27'])).
% 0.47/0.63  thf('52', plain,
% 0.47/0.63      ((v1_subset_1 @ sk_B_1 @ 
% 0.47/0.63        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('53', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('54', plain,
% 0.47/0.63      ((v1_subset_1 @ sk_B_1 @ 
% 0.47/0.63        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('demod', [status(thm)], ['52', '53'])).
% 0.47/0.63  thf('55', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['49', '50', '51', '54'])).
% 0.47/0.63  thf('56', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['41', '55'])).
% 0.47/0.63  thf('57', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ sk_A)
% 0.47/0.63          | (v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['40', '56'])).
% 0.47/0.63  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('59', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['57', '58'])).
% 0.47/0.63  thf('60', plain,
% 0.47/0.63      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['39', '59'])).
% 0.47/0.63  thf('61', plain,
% 0.47/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['38', '60'])).
% 0.47/0.63  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('63', plain,
% 0.47/0.63      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['61', '62'])).
% 0.47/0.63  thf('64', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('65', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.63      inference('demod', [status(thm)], ['5', '10'])).
% 0.47/0.63  thf('66', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('67', plain,
% 0.47/0.63      (![X1 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.63  thf('68', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B_1 @ 
% 0.47/0.63        (k1_zfmisc_1 @ 
% 0.47/0.63         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.47/0.63      inference('demod', [status(thm)], ['14', '15'])).
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
% 0.47/0.63  thf('69', plain,
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
% 0.47/0.63          | (l1_waybel_0 @ (k3_yellow19 @ X8 @ X7 @ X9) @ X8))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.47/0.63  thf('70', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('71', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('72', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('73', plain,
% 0.47/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.47/0.63          | (v1_xboole_0 @ X7)
% 0.47/0.63          | ~ (l1_struct_0 @ X8)
% 0.47/0.63          | (v2_struct_0 @ X8)
% 0.47/0.63          | (v1_xboole_0 @ X9)
% 0.47/0.63          | ~ (v2_waybel_0 @ X9 @ (k3_lattice3 @ (k1_lattice3 @ X7)))
% 0.47/0.63          | ~ (v13_waybel_0 @ X9 @ (k3_lattice3 @ (k1_lattice3 @ X7)))
% 0.47/0.63          | ~ (m1_subset_1 @ X9 @ 
% 0.47/0.63               (k1_zfmisc_1 @ 
% 0.47/0.63                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X7)))))
% 0.47/0.63          | (l1_waybel_0 @ (k3_yellow19 @ X8 @ X7 @ X9) @ X8))),
% 0.47/0.63      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.47/0.63  thf('74', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.47/0.63           X0)
% 0.47/0.63          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['68', '73'])).
% 0.47/0.63  thf('75', plain,
% 0.47/0.63      ((v13_waybel_0 @ sk_B_1 @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['23', '24'])).
% 0.47/0.63  thf('76', plain,
% 0.47/0.63      ((v2_waybel_0 @ sk_B_1 @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['26', '27'])).
% 0.47/0.63  thf('77', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.47/0.63           X0)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.47/0.63  thf('78', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (l1_waybel_0 @ 
% 0.47/0.63             (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['67', '77'])).
% 0.47/0.63  thf('79', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ sk_A)
% 0.47/0.63          | (l1_waybel_0 @ 
% 0.47/0.63             (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['66', '78'])).
% 0.47/0.63  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('81', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.47/0.63           X0)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['79', '80'])).
% 0.47/0.63  thf('82', plain,
% 0.47/0.63      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | (l1_waybel_0 @ 
% 0.47/0.63           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['65', '81'])).
% 0.47/0.63  thf('83', plain,
% 0.47/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | (l1_waybel_0 @ 
% 0.47/0.63           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['64', '82'])).
% 0.47/0.63  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('85', plain,
% 0.47/0.63      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.47/0.63         sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['83', '84'])).
% 0.47/0.63  thf('86', plain,
% 0.47/0.63      (((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.47/0.63        | (r2_hidden @ sk_C @ 
% 0.47/0.63           (k10_yellow_6 @ sk_A @ 
% 0.47/0.63            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('87', plain,
% 0.47/0.63      (((r2_hidden @ sk_C @ 
% 0.47/0.63         (k10_yellow_6 @ sk_A @ 
% 0.47/0.63          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 0.47/0.63         <= (((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.47/0.63      inference('split', [status(esa)], ['86'])).
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
% 0.47/0.63  thf('88', plain,
% 0.47/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.63         ((v2_struct_0 @ X16)
% 0.47/0.63          | ~ (v4_orders_2 @ X16)
% 0.47/0.63          | ~ (v7_waybel_0 @ X16)
% 0.47/0.63          | ~ (l1_waybel_0 @ X16 @ X17)
% 0.47/0.63          | ~ (r2_hidden @ X18 @ (k10_yellow_6 @ X17 @ X16))
% 0.47/0.63          | (r2_waybel_7 @ X17 @ (k2_yellow19 @ X17 @ X16) @ X18)
% 0.47/0.63          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.47/0.63          | ~ (l1_pre_topc @ X17)
% 0.47/0.63          | ~ (v2_pre_topc @ X17)
% 0.47/0.63          | (v2_struct_0 @ X17))),
% 0.47/0.63      inference('cnf', [status(esa)], [t13_yellow19])).
% 0.47/0.63  thf('89', plain,
% 0.47/0.63      ((((v2_struct_0 @ sk_A)
% 0.47/0.63         | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63         | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | (r2_waybel_7 @ sk_A @ 
% 0.47/0.63            (k2_yellow19 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.47/0.63            sk_C)
% 0.47/0.63         | ~ (l1_waybel_0 @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.47/0.63         | ~ (v7_waybel_0 @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63         | ~ (v4_orders_2 @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 0.47/0.63         <= (((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['87', '88'])).
% 0.47/0.63  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('92', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('93', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('94', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B_1 @ 
% 0.47/0.63        (k1_zfmisc_1 @ 
% 0.47/0.63         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.47/0.63      inference('demod', [status(thm)], ['14', '15'])).
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
% 0.47/0.63  thf('95', plain,
% 0.47/0.63      (![X19 : $i, X20 : $i]:
% 0.47/0.63         ((v1_xboole_0 @ X19)
% 0.47/0.63          | ~ (v1_subset_1 @ X19 @ 
% 0.47/0.63               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X20))))
% 0.47/0.63          | ~ (v2_waybel_0 @ X19 @ (k3_yellow_1 @ (k2_struct_0 @ X20)))
% 0.47/0.63          | ~ (v13_waybel_0 @ X19 @ (k3_yellow_1 @ (k2_struct_0 @ X20)))
% 0.47/0.63          | ~ (m1_subset_1 @ X19 @ 
% 0.47/0.63               (k1_zfmisc_1 @ 
% 0.47/0.63                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X20)))))
% 0.47/0.63          | ((X19)
% 0.47/0.63              = (k2_yellow19 @ X20 @ 
% 0.47/0.63                 (k3_yellow19 @ X20 @ (k2_struct_0 @ X20) @ X19)))
% 0.47/0.63          | ~ (l1_struct_0 @ X20)
% 0.47/0.63          | (v2_struct_0 @ X20))),
% 0.47/0.63      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.47/0.63  thf('96', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('97', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('98', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('99', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('100', plain,
% 0.47/0.63      (![X19 : $i, X20 : $i]:
% 0.47/0.63         ((v1_xboole_0 @ X19)
% 0.47/0.63          | ~ (v1_subset_1 @ X19 @ 
% 0.47/0.63               (u1_struct_0 @ 
% 0.47/0.63                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X20)))))
% 0.47/0.63          | ~ (v2_waybel_0 @ X19 @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X20))))
% 0.47/0.63          | ~ (v13_waybel_0 @ X19 @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X20))))
% 0.47/0.63          | ~ (m1_subset_1 @ X19 @ 
% 0.47/0.63               (k1_zfmisc_1 @ 
% 0.47/0.63                (u1_struct_0 @ 
% 0.47/0.63                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X20))))))
% 0.47/0.63          | ((X19)
% 0.47/0.63              = (k2_yellow19 @ X20 @ 
% 0.47/0.63                 (k3_yellow19 @ X20 @ (k2_struct_0 @ X20) @ X19)))
% 0.47/0.63          | ~ (l1_struct_0 @ X20)
% 0.47/0.63          | (v2_struct_0 @ X20))),
% 0.47/0.63      inference('demod', [status(thm)], ['95', '96', '97', '98', '99'])).
% 0.47/0.63  thf('101', plain,
% 0.47/0.63      (((v2_struct_0 @ sk_A)
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | ((sk_B_1)
% 0.47/0.63            = (k2_yellow19 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.47/0.63             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.47/0.63             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63        | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.47/0.63             (u1_struct_0 @ 
% 0.47/0.63              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1))),
% 0.47/0.63      inference('sup-', [status(thm)], ['94', '100'])).
% 0.47/0.63  thf('102', plain,
% 0.47/0.63      ((v13_waybel_0 @ sk_B_1 @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['23', '24'])).
% 0.47/0.63  thf('103', plain,
% 0.47/0.63      ((v2_waybel_0 @ sk_B_1 @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['26', '27'])).
% 0.47/0.63  thf('104', plain,
% 0.47/0.63      ((v1_subset_1 @ sk_B_1 @ 
% 0.47/0.63        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('demod', [status(thm)], ['52', '53'])).
% 0.47/0.63  thf('105', plain,
% 0.47/0.63      (((v2_struct_0 @ sk_A)
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | ((sk_B_1)
% 0.47/0.63            = (k2_yellow19 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1))),
% 0.47/0.63      inference('demod', [status(thm)], ['101', '102', '103', '104'])).
% 0.47/0.63  thf('106', plain,
% 0.47/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | ((sk_B_1)
% 0.47/0.63            = (k2_yellow19 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63        | (v2_struct_0 @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['93', '105'])).
% 0.47/0.63  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('108', plain,
% 0.47/0.63      (((v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | ((sk_B_1)
% 0.47/0.63            = (k2_yellow19 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63        | (v2_struct_0 @ sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['106', '107'])).
% 0.47/0.63  thf('109', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('110', plain,
% 0.47/0.63      (((v2_struct_0 @ sk_A)
% 0.47/0.63        | ((sk_B_1)
% 0.47/0.63            = (k2_yellow19 @ sk_A @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.47/0.63      inference('clc', [status(thm)], ['108', '109'])).
% 0.47/0.63  thf('111', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('112', plain,
% 0.47/0.63      (((sk_B_1)
% 0.47/0.63         = (k2_yellow19 @ sk_A @ 
% 0.47/0.63            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.63      inference('clc', [status(thm)], ['110', '111'])).
% 0.47/0.63  thf('113', plain,
% 0.47/0.63      ((((v2_struct_0 @ sk_A)
% 0.47/0.63         | (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.47/0.63         | ~ (l1_waybel_0 @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.47/0.63         | ~ (v7_waybel_0 @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63         | ~ (v4_orders_2 @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 0.47/0.63         <= (((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.47/0.63      inference('demod', [status(thm)], ['89', '90', '91', '92', '112'])).
% 0.47/0.63  thf('114', plain,
% 0.47/0.63      ((~ (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.47/0.63        | ~ (r2_hidden @ sk_C @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('115', plain,
% 0.47/0.63      (~ ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)) | 
% 0.47/0.63       ~
% 0.47/0.63       ((r2_hidden @ sk_C @ 
% 0.47/0.63         (k10_yellow_6 @ sk_A @ 
% 0.47/0.63          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.47/0.63      inference('split', [status(esa)], ['114'])).
% 0.47/0.63  thf('116', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('117', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('118', plain,
% 0.47/0.63      (![X1 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.63  thf('119', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('120', plain,
% 0.47/0.63      (((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C))
% 0.47/0.63         <= (((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.63      inference('split', [status(esa)], ['86'])).
% 0.47/0.63  thf('121', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('122', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('123', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.63      inference('demod', [status(thm)], ['5', '10'])).
% 0.47/0.63  thf('124', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('125', plain,
% 0.47/0.63      (![X1 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.63  thf('126', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B_1 @ 
% 0.47/0.63        (k1_zfmisc_1 @ 
% 0.47/0.63         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.47/0.63      inference('demod', [status(thm)], ['14', '15'])).
% 0.47/0.63  thf('127', plain,
% 0.47/0.63      (((m1_subset_1 @ sk_B_1 @ 
% 0.47/0.63         (k1_zfmisc_1 @ 
% 0.47/0.63          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.63      inference('sup+', [status(thm)], ['125', '126'])).
% 0.47/0.63  thf('128', plain,
% 0.47/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | (m1_subset_1 @ sk_B_1 @ 
% 0.47/0.63           (k1_zfmisc_1 @ 
% 0.47/0.63            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['124', '127'])).
% 0.47/0.63  thf('129', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('130', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B_1 @ 
% 0.47/0.63        (k1_zfmisc_1 @ 
% 0.47/0.63         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.47/0.63      inference('demod', [status(thm)], ['128', '129'])).
% 0.47/0.63  thf('131', plain,
% 0.47/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.47/0.63          | (v1_xboole_0 @ X13)
% 0.47/0.63          | ~ (l1_struct_0 @ X14)
% 0.47/0.63          | (v2_struct_0 @ X14)
% 0.47/0.63          | (v1_xboole_0 @ X15)
% 0.47/0.63          | ~ (v1_subset_1 @ X15 @ 
% 0.47/0.63               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X13))))
% 0.47/0.63          | ~ (v2_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.47/0.63          | ~ (v13_waybel_0 @ X15 @ (k3_lattice3 @ (k1_lattice3 @ X13)))
% 0.47/0.63          | ~ (m1_subset_1 @ X15 @ 
% 0.47/0.63               (k1_zfmisc_1 @ 
% 0.47/0.63                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X13)))))
% 0.47/0.63          | (v7_waybel_0 @ (k3_yellow19 @ X14 @ X13 @ X15)))),
% 0.47/0.63      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.47/0.63  thf('132', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63          | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.47/0.63               (u1_struct_0 @ 
% 0.47/0.63                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['130', '131'])).
% 0.47/0.63  thf('133', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('134', plain,
% 0.47/0.63      (![X1 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.63  thf('135', plain,
% 0.47/0.63      ((v13_waybel_0 @ sk_B_1 @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['23', '24'])).
% 0.47/0.63  thf('136', plain,
% 0.47/0.63      (((v13_waybel_0 @ sk_B_1 @ 
% 0.47/0.63         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.63      inference('sup+', [status(thm)], ['134', '135'])).
% 0.47/0.63  thf('137', plain,
% 0.47/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | (v13_waybel_0 @ sk_B_1 @ 
% 0.47/0.63           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['133', '136'])).
% 0.47/0.63  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('139', plain,
% 0.47/0.63      ((v13_waybel_0 @ sk_B_1 @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['137', '138'])).
% 0.47/0.63  thf('140', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('141', plain,
% 0.47/0.63      (![X1 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.63  thf('142', plain,
% 0.47/0.63      ((v2_waybel_0 @ sk_B_1 @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['26', '27'])).
% 0.47/0.63  thf('143', plain,
% 0.47/0.63      (((v2_waybel_0 @ sk_B_1 @ 
% 0.47/0.63         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.63      inference('sup+', [status(thm)], ['141', '142'])).
% 0.47/0.63  thf('144', plain,
% 0.47/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | (v2_waybel_0 @ sk_B_1 @ 
% 0.47/0.63           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['140', '143'])).
% 0.47/0.63  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('146', plain,
% 0.47/0.63      ((v2_waybel_0 @ sk_B_1 @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['144', '145'])).
% 0.47/0.63  thf('147', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('148', plain,
% 0.47/0.63      (![X1 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.63  thf('149', plain,
% 0.47/0.63      ((v1_subset_1 @ sk_B_1 @ 
% 0.47/0.63        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('demod', [status(thm)], ['52', '53'])).
% 0.47/0.63  thf('150', plain,
% 0.47/0.63      (((v1_subset_1 @ sk_B_1 @ 
% 0.47/0.63         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.63      inference('sup+', [status(thm)], ['148', '149'])).
% 0.47/0.63  thf('151', plain,
% 0.47/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | (v1_subset_1 @ sk_B_1 @ 
% 0.47/0.63           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['147', '150'])).
% 0.47/0.63  thf('152', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('153', plain,
% 0.47/0.63      ((v1_subset_1 @ sk_B_1 @ 
% 0.47/0.63        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.47/0.63      inference('demod', [status(thm)], ['151', '152'])).
% 0.47/0.63  thf('154', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['132', '139', '146', '153'])).
% 0.47/0.63  thf('155', plain,
% 0.47/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['123', '154'])).
% 0.47/0.63  thf('156', plain,
% 0.47/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['122', '155'])).
% 0.47/0.63  thf('157', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('158', plain,
% 0.47/0.63      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['156', '157'])).
% 0.47/0.63  thf('159', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('160', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.63      inference('demod', [status(thm)], ['5', '10'])).
% 0.47/0.63  thf('161', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B_1 @ 
% 0.47/0.63        (k1_zfmisc_1 @ 
% 0.47/0.63         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.47/0.63      inference('demod', [status(thm)], ['128', '129'])).
% 0.47/0.63  thf('162', plain,
% 0.47/0.63      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.47/0.63          | (v1_xboole_0 @ X10)
% 0.47/0.63          | ~ (l1_struct_0 @ X11)
% 0.47/0.63          | (v2_struct_0 @ X11)
% 0.47/0.63          | (v1_xboole_0 @ X12)
% 0.47/0.63          | ~ (v2_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.47/0.63          | ~ (v13_waybel_0 @ X12 @ (k3_lattice3 @ (k1_lattice3 @ X10)))
% 0.47/0.63          | ~ (m1_subset_1 @ X12 @ 
% 0.47/0.63               (k1_zfmisc_1 @ 
% 0.47/0.63                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X10)))))
% 0.47/0.63          | (v4_orders_2 @ (k3_yellow19 @ X11 @ X10 @ X12)))),
% 0.47/0.63      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.47/0.63  thf('163', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['161', '162'])).
% 0.47/0.63  thf('164', plain,
% 0.47/0.63      ((v13_waybel_0 @ sk_B_1 @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['137', '138'])).
% 0.47/0.63  thf('165', plain,
% 0.47/0.63      ((v2_waybel_0 @ sk_B_1 @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['144', '145'])).
% 0.47/0.63  thf('166', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['163', '164', '165'])).
% 0.47/0.63  thf('167', plain,
% 0.47/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['160', '166'])).
% 0.47/0.63  thf('168', plain,
% 0.47/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['159', '167'])).
% 0.47/0.63  thf('169', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('170', plain,
% 0.47/0.63      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['168', '169'])).
% 0.47/0.63  thf('171', plain,
% 0.47/0.63      (![X1 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.63  thf('172', plain,
% 0.47/0.63      (![X1 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.63  thf('173', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('174', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.63      inference('demod', [status(thm)], ['5', '10'])).
% 0.47/0.63  thf('175', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B_1 @ 
% 0.47/0.63        (k1_zfmisc_1 @ 
% 0.47/0.63         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.47/0.63      inference('demod', [status(thm)], ['128', '129'])).
% 0.47/0.63  thf('176', plain,
% 0.47/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.47/0.63          | (v1_xboole_0 @ X7)
% 0.47/0.63          | ~ (l1_struct_0 @ X8)
% 0.47/0.63          | (v2_struct_0 @ X8)
% 0.47/0.63          | (v1_xboole_0 @ X9)
% 0.47/0.63          | ~ (v2_waybel_0 @ X9 @ (k3_lattice3 @ (k1_lattice3 @ X7)))
% 0.47/0.63          | ~ (v13_waybel_0 @ X9 @ (k3_lattice3 @ (k1_lattice3 @ X7)))
% 0.47/0.63          | ~ (m1_subset_1 @ X9 @ 
% 0.47/0.63               (k1_zfmisc_1 @ 
% 0.47/0.63                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X7)))))
% 0.47/0.63          | (l1_waybel_0 @ (k3_yellow19 @ X8 @ X7 @ X9) @ X8))),
% 0.47/0.63      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.47/0.63  thf('177', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.47/0.63           X0)
% 0.47/0.63          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['175', '176'])).
% 0.47/0.63  thf('178', plain,
% 0.47/0.63      ((v13_waybel_0 @ sk_B_1 @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['137', '138'])).
% 0.47/0.63  thf('179', plain,
% 0.47/0.63      ((v2_waybel_0 @ sk_B_1 @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['144', '145'])).
% 0.47/0.63  thf('180', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.47/0.63           X0)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['177', '178', '179'])).
% 0.47/0.63  thf('181', plain,
% 0.47/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | (l1_waybel_0 @ 
% 0.47/0.63           (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['174', '180'])).
% 0.47/0.63  thf('182', plain,
% 0.47/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.63        | (l1_waybel_0 @ 
% 0.47/0.63           (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['173', '181'])).
% 0.47/0.63  thf('183', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('184', plain,
% 0.47/0.63      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.47/0.63         sk_A)
% 0.47/0.63        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63        | (v2_struct_0 @ sk_A)
% 0.47/0.63        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['182', '183'])).
% 0.47/0.63  thf('185', plain,
% 0.47/0.63      (![X1 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.63  thf('186', plain,
% 0.47/0.63      (((sk_B_1)
% 0.47/0.63         = (k2_yellow19 @ sk_A @ 
% 0.47/0.63            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.63      inference('clc', [status(thm)], ['110', '111'])).
% 0.47/0.63  thf('187', plain,
% 0.47/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.63         ((v2_struct_0 @ X16)
% 0.47/0.63          | ~ (v4_orders_2 @ X16)
% 0.47/0.63          | ~ (v7_waybel_0 @ X16)
% 0.47/0.63          | ~ (l1_waybel_0 @ X16 @ X17)
% 0.47/0.63          | ~ (r2_waybel_7 @ X17 @ (k2_yellow19 @ X17 @ X16) @ X18)
% 0.47/0.63          | (r2_hidden @ X18 @ (k10_yellow_6 @ X17 @ X16))
% 0.47/0.63          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.47/0.63          | ~ (l1_pre_topc @ X17)
% 0.47/0.63          | ~ (v2_pre_topc @ X17)
% 0.47/0.63          | (v2_struct_0 @ X17))),
% 0.47/0.63      inference('cnf', [status(esa)], [t13_yellow19])).
% 0.47/0.63  thf('188', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | ~ (v2_pre_topc @ sk_A)
% 0.47/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63          | ~ (l1_waybel_0 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.47/0.63          | ~ (v7_waybel_0 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (v4_orders_2 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['186', '187'])).
% 0.47/0.63  thf('189', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('190', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('191', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63          | ~ (l1_waybel_0 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.47/0.63          | ~ (v7_waybel_0 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (v4_orders_2 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.63      inference('demod', [status(thm)], ['188', '189', '190'])).
% 0.47/0.63  thf('192', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_waybel_0 @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (v4_orders_2 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (v7_waybel_0 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | ~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['185', '191'])).
% 0.47/0.63  thf('193', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | ~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63          | ~ (v7_waybel_0 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (v4_orders_2 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['184', '192'])).
% 0.47/0.63  thf('194', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (v4_orders_2 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (v7_waybel_0 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('simplify', [status(thm)], ['193'])).
% 0.47/0.63  thf('195', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | ~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63          | ~ (v7_waybel_0 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['172', '194'])).
% 0.47/0.63  thf('196', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (v7_waybel_0 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | ~ (v4_orders_2 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.63      inference('simplify', [status(thm)], ['195'])).
% 0.47/0.63  thf('197', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | ~ (v4_orders_2 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | ~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['171', '196'])).
% 0.47/0.63  thf('198', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (v4_orders_2 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | ~ (v7_waybel_0 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.63      inference('simplify', [status(thm)], ['197'])).
% 0.47/0.63  thf('199', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | ~ (v7_waybel_0 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | ~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['170', '198'])).
% 0.47/0.63  thf('200', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | ~ (v7_waybel_0 @ 
% 0.47/0.63               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('simplify', [status(thm)], ['199'])).
% 0.47/0.63  thf('201', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | ~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['158', '200'])).
% 0.47/0.63  thf('202', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | ~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.63      inference('simplify', [status(thm)], ['201'])).
% 0.47/0.63  thf('203', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | ~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['121', '202'])).
% 0.47/0.63  thf('204', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('205', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (v2_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | ~ (r2_waybel_7 @ sk_A @ sk_B_1 @ X0)
% 0.47/0.63          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63          | (r2_hidden @ X0 @ 
% 0.47/0.63             (k10_yellow_6 @ sk_A @ 
% 0.47/0.63              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.63      inference('demod', [status(thm)], ['203', '204'])).
% 0.47/0.63  thf('206', plain,
% 0.47/0.63      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63         | (r2_hidden @ sk_C @ 
% 0.47/0.63            (k10_yellow_6 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63         <= (((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['120', '205'])).
% 0.47/0.63  thf('207', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('208', plain,
% 0.47/0.63      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63         | (r2_hidden @ sk_C @ 
% 0.47/0.63            (k10_yellow_6 @ sk_A @ 
% 0.47/0.63             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.47/0.63         | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.47/0.63         <= (((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.63      inference('demod', [status(thm)], ['206', '207'])).
% 0.47/0.63  thf('209', plain,
% 0.47/0.63      ((~ (r2_hidden @ sk_C @ 
% 0.47/0.63           (k10_yellow_6 @ sk_A @ 
% 0.47/0.63            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.47/0.63      inference('split', [status(esa)], ['114'])).
% 0.47/0.63  thf('210', plain,
% 0.47/0.63      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.63         | (v2_struct_0 @ sk_A)
% 0.47/0.63         | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))
% 0.47/0.63         <= (~
% 0.47/0.63             ((r2_hidden @ sk_C @ 
% 0.47/0.63               (k10_yellow_6 @ sk_A @ 
% 0.47/0.63                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.47/0.63             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['208', '209'])).
% 0.47/0.63  thf('211', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.47/0.63      inference('demod', [status(thm)], ['5', '10'])).
% 0.47/0.63  thf('212', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.47/0.63  thf('213', plain,
% 0.47/0.63      (![X1 : $i]:
% 0.47/0.63         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.47/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.63  thf('214', plain,
% 0.47/0.63      ((m1_subset_1 @ sk_B_1 @ 
% 0.47/0.63        (k1_zfmisc_1 @ 
% 0.47/0.63         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.47/0.63      inference('demod', [status(thm)], ['14', '15'])).
% 0.47/0.63  thf('215', plain,
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
% 0.47/0.63          | ~ (v2_struct_0 @ (k3_yellow19 @ X8 @ X7 @ X9)))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.47/0.63  thf('216', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('217', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('218', plain,
% 0.47/0.63      (![X4 : $i]: ((k3_yellow_1 @ X4) = (k3_lattice3 @ (k1_lattice3 @ X4)))),
% 0.47/0.63      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.47/0.63  thf('219', plain,
% 0.47/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.47/0.63          | (v1_xboole_0 @ X7)
% 0.47/0.63          | ~ (l1_struct_0 @ X8)
% 0.47/0.63          | (v2_struct_0 @ X8)
% 0.47/0.63          | (v1_xboole_0 @ X9)
% 0.47/0.63          | ~ (v2_waybel_0 @ X9 @ (k3_lattice3 @ (k1_lattice3 @ X7)))
% 0.47/0.63          | ~ (v13_waybel_0 @ X9 @ (k3_lattice3 @ (k1_lattice3 @ X7)))
% 0.47/0.63          | ~ (m1_subset_1 @ X9 @ 
% 0.47/0.63               (k1_zfmisc_1 @ 
% 0.47/0.63                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X7)))))
% 0.47/0.63          | ~ (v2_struct_0 @ (k3_yellow19 @ X8 @ X7 @ X9)))),
% 0.47/0.63      inference('demod', [status(thm)], ['215', '216', '217', '218'])).
% 0.47/0.63  thf('220', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.47/0.63               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['214', '219'])).
% 0.47/0.63  thf('221', plain,
% 0.47/0.63      ((v13_waybel_0 @ sk_B_1 @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['23', '24'])).
% 0.47/0.63  thf('222', plain,
% 0.47/0.63      ((v2_waybel_0 @ sk_B_1 @ 
% 0.47/0.63        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.47/0.63      inference('demod', [status(thm)], ['26', '27'])).
% 0.47/0.63  thf('223', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.63          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['220', '221', '222'])).
% 0.47/0.63  thf('224', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.47/0.63          | ~ (l1_struct_0 @ sk_A)
% 0.47/0.63          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.63          | ~ (l1_struct_0 @ X0)
% 0.47/0.63          | (v2_struct_0 @ X0)
% 0.47/0.64          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['213', '223'])).
% 0.47/0.64  thf('225', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (l1_pre_topc @ sk_A)
% 0.47/0.64          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.64          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64          | (v2_struct_0 @ X0)
% 0.47/0.64          | ~ (l1_struct_0 @ X0)
% 0.47/0.64          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.64          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.64               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['212', '224'])).
% 0.47/0.64  thf('226', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('227', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.64          | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64          | (v2_struct_0 @ X0)
% 0.47/0.64          | ~ (l1_struct_0 @ X0)
% 0.47/0.64          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.64          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.64               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.47/0.64      inference('demod', [status(thm)], ['225', '226'])).
% 0.47/0.64  thf('228', plain,
% 0.47/0.64      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.64        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.64        | (v2_struct_0 @ sk_A)
% 0.47/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['211', '227'])).
% 0.47/0.64  thf('229', plain,
% 0.47/0.64      ((((v1_xboole_0 @ sk_B_1)
% 0.47/0.64         | (v2_struct_0 @ sk_A)
% 0.47/0.64         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.64         | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64         | (v2_struct_0 @ sk_A)
% 0.47/0.64         | ~ (l1_struct_0 @ sk_A)
% 0.47/0.64         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.47/0.64         <= (~
% 0.47/0.64             ((r2_hidden @ sk_C @ 
% 0.47/0.64               (k10_yellow_6 @ sk_A @ 
% 0.47/0.64                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.47/0.64             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['210', '228'])).
% 0.47/0.64  thf('230', plain,
% 0.47/0.64      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.64         | ~ (l1_struct_0 @ sk_A)
% 0.47/0.64         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.64         | (v2_struct_0 @ sk_A)
% 0.47/0.64         | (v1_xboole_0 @ sk_B_1)))
% 0.47/0.64         <= (~
% 0.47/0.64             ((r2_hidden @ sk_C @ 
% 0.47/0.64               (k10_yellow_6 @ sk_A @ 
% 0.47/0.64                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.47/0.64             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['229'])).
% 0.47/0.64  thf('231', plain,
% 0.47/0.64      (((~ (l1_pre_topc @ sk_A)
% 0.47/0.64         | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64         | (v2_struct_0 @ sk_A)
% 0.47/0.64         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.64         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.47/0.64         <= (~
% 0.47/0.64             ((r2_hidden @ sk_C @ 
% 0.47/0.64               (k10_yellow_6 @ sk_A @ 
% 0.47/0.64                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.47/0.64             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['119', '230'])).
% 0.47/0.64  thf('232', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('233', plain,
% 0.47/0.64      ((((v1_xboole_0 @ sk_B_1)
% 0.47/0.64         | (v2_struct_0 @ sk_A)
% 0.47/0.64         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.64         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.47/0.64         <= (~
% 0.47/0.64             ((r2_hidden @ sk_C @ 
% 0.47/0.64               (k10_yellow_6 @ sk_A @ 
% 0.47/0.64                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.47/0.64             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.64      inference('demod', [status(thm)], ['231', '232'])).
% 0.47/0.64  thf('234', plain,
% 0.47/0.64      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.64         | ~ (l1_struct_0 @ sk_A)
% 0.47/0.64         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.64         | (v2_struct_0 @ sk_A)
% 0.47/0.64         | (v1_xboole_0 @ sk_B_1)))
% 0.47/0.64         <= (~
% 0.47/0.64             ((r2_hidden @ sk_C @ 
% 0.47/0.64               (k10_yellow_6 @ sk_A @ 
% 0.47/0.64                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.47/0.64             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.64      inference('sup+', [status(thm)], ['118', '233'])).
% 0.47/0.64  thf('235', plain,
% 0.47/0.64      ((((v1_xboole_0 @ sk_B_1)
% 0.47/0.64         | (v2_struct_0 @ sk_A)
% 0.47/0.64         | ~ (l1_struct_0 @ sk_A)
% 0.47/0.64         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.47/0.64         <= (~
% 0.47/0.64             ((r2_hidden @ sk_C @ 
% 0.47/0.64               (k10_yellow_6 @ sk_A @ 
% 0.47/0.64                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.47/0.64             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['234'])).
% 0.47/0.64  thf('236', plain,
% 0.47/0.64      (((~ (l1_pre_topc @ sk_A)
% 0.47/0.64         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.64         | (v2_struct_0 @ sk_A)
% 0.47/0.64         | (v1_xboole_0 @ sk_B_1)))
% 0.47/0.64         <= (~
% 0.47/0.64             ((r2_hidden @ sk_C @ 
% 0.47/0.64               (k10_yellow_6 @ sk_A @ 
% 0.47/0.64                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.47/0.64             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['117', '235'])).
% 0.47/0.64  thf('237', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('238', plain,
% 0.47/0.64      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.47/0.64         | (v2_struct_0 @ sk_A)
% 0.47/0.64         | (v1_xboole_0 @ sk_B_1)))
% 0.47/0.64         <= (~
% 0.47/0.64             ((r2_hidden @ sk_C @ 
% 0.47/0.64               (k10_yellow_6 @ sk_A @ 
% 0.47/0.64                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.47/0.64             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.64      inference('demod', [status(thm)], ['236', '237'])).
% 0.47/0.64  thf('239', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('240', plain,
% 0.47/0.64      ((((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.47/0.64         <= (~
% 0.47/0.64             ((r2_hidden @ sk_C @ 
% 0.47/0.64               (k10_yellow_6 @ sk_A @ 
% 0.47/0.64                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.47/0.64             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.64      inference('clc', [status(thm)], ['238', '239'])).
% 0.47/0.64  thf('241', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('242', plain,
% 0.47/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.47/0.64         <= (~
% 0.47/0.64             ((r2_hidden @ sk_C @ 
% 0.47/0.64               (k10_yellow_6 @ sk_A @ 
% 0.47/0.64                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.47/0.64             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.64      inference('clc', [status(thm)], ['240', '241'])).
% 0.47/0.64  thf(fc2_struct_0, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.47/0.64       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.47/0.64  thf('243', plain,
% 0.47/0.64      (![X3 : $i]:
% 0.47/0.64         (~ (v1_xboole_0 @ (u1_struct_0 @ X3))
% 0.47/0.64          | ~ (l1_struct_0 @ X3)
% 0.47/0.64          | (v2_struct_0 @ X3))),
% 0.47/0.64      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.47/0.64  thf('244', plain,
% 0.47/0.64      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.47/0.64         <= (~
% 0.47/0.64             ((r2_hidden @ sk_C @ 
% 0.47/0.64               (k10_yellow_6 @ sk_A @ 
% 0.47/0.64                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.47/0.64             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['242', '243'])).
% 0.47/0.64  thf('245', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('246', plain,
% 0.47/0.64      ((~ (l1_struct_0 @ sk_A))
% 0.47/0.64         <= (~
% 0.47/0.64             ((r2_hidden @ sk_C @ 
% 0.47/0.64               (k10_yellow_6 @ sk_A @ 
% 0.47/0.64                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.47/0.64             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.64      inference('clc', [status(thm)], ['244', '245'])).
% 0.47/0.64  thf('247', plain,
% 0.47/0.64      ((~ (l1_pre_topc @ sk_A))
% 0.47/0.64         <= (~
% 0.47/0.64             ((r2_hidden @ sk_C @ 
% 0.47/0.64               (k10_yellow_6 @ sk_A @ 
% 0.47/0.64                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) & 
% 0.47/0.64             ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['116', '246'])).
% 0.47/0.64  thf('248', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('249', plain,
% 0.47/0.64      (((r2_hidden @ sk_C @ 
% 0.47/0.64         (k10_yellow_6 @ sk_A @ 
% 0.47/0.64          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) | 
% 0.47/0.64       ~ ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C))),
% 0.47/0.64      inference('demod', [status(thm)], ['247', '248'])).
% 0.47/0.64  thf('250', plain,
% 0.47/0.64      (((r2_hidden @ sk_C @ 
% 0.47/0.64         (k10_yellow_6 @ sk_A @ 
% 0.47/0.64          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))) | 
% 0.47/0.64       ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C))),
% 0.47/0.64      inference('split', [status(esa)], ['86'])).
% 0.47/0.64  thf('251', plain,
% 0.47/0.64      (((r2_hidden @ sk_C @ 
% 0.47/0.64         (k10_yellow_6 @ sk_A @ 
% 0.47/0.64          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.47/0.64      inference('sat_resolution*', [status(thm)], ['115', '249', '250'])).
% 0.47/0.64  thf('252', plain,
% 0.47/0.64      (((v2_struct_0 @ sk_A)
% 0.47/0.64        | (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.47/0.64        | ~ (l1_waybel_0 @ 
% 0.47/0.64             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.47/0.64        | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.64        | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.64        | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.64      inference('simpl_trail', [status(thm)], ['113', '251'])).
% 0.47/0.64  thf('253', plain,
% 0.47/0.64      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.64        | (v2_struct_0 @ sk_A)
% 0.47/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64        | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.64        | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.64        | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.64        | (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.47/0.64        | (v2_struct_0 @ sk_A))),
% 0.47/0.64      inference('sup-', [status(thm)], ['85', '252'])).
% 0.47/0.64  thf('254', plain,
% 0.47/0.64      (((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.47/0.64        | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.64        | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.64        | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64        | (v2_struct_0 @ sk_A)
% 0.47/0.64        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['253'])).
% 0.47/0.64  thf('255', plain,
% 0.47/0.64      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.64        | (v2_struct_0 @ sk_A)
% 0.47/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.64        | (v2_struct_0 @ sk_A)
% 0.47/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64        | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.64        | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.64        | (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C))),
% 0.47/0.64      inference('sup-', [status(thm)], ['63', '254'])).
% 0.47/0.64  thf('256', plain,
% 0.47/0.64      (((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.47/0.64        | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.64        | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64        | (v2_struct_0 @ sk_A)
% 0.47/0.64        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['255'])).
% 0.47/0.64  thf('257', plain,
% 0.47/0.64      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.64        | (v2_struct_0 @ sk_A)
% 0.47/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.64        | (v2_struct_0 @ sk_A)
% 0.47/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64        | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.64        | (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C))),
% 0.47/0.64      inference('sup-', [status(thm)], ['37', '256'])).
% 0.47/0.64  thf('258', plain,
% 0.47/0.64      (((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.47/0.64        | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 0.47/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64        | (v2_struct_0 @ sk_A)
% 0.47/0.64        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['257'])).
% 0.47/0.64  thf('259', plain,
% 0.47/0.64      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.64        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.64        | (v2_struct_0 @ sk_A)
% 0.47/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['211', '227'])).
% 0.47/0.64  thf('260', plain,
% 0.47/0.64      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.64        | (v2_struct_0 @ sk_A)
% 0.47/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64        | (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.47/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64        | (v2_struct_0 @ sk_A)
% 0.47/0.64        | ~ (l1_struct_0 @ sk_A)
% 0.47/0.64        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['258', '259'])).
% 0.47/0.64  thf('261', plain,
% 0.47/0.64      ((~ (l1_struct_0 @ sk_A)
% 0.47/0.64        | (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)
% 0.47/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64        | (v2_struct_0 @ sk_A)
% 0.47/0.64        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['260'])).
% 0.47/0.64  thf('262', plain,
% 0.47/0.64      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.64        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.64        | (v2_struct_0 @ sk_A)
% 0.47/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64        | (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C))),
% 0.47/0.64      inference('sup-', [status(thm)], ['3', '261'])).
% 0.47/0.64  thf('263', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('264', plain,
% 0.47/0.64      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.47/0.64        | (v2_struct_0 @ sk_A)
% 0.47/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.64        | (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C))),
% 0.47/0.64      inference('demod', [status(thm)], ['262', '263'])).
% 0.47/0.64  thf('265', plain,
% 0.47/0.64      ((~ (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C))
% 0.47/0.64         <= (~ ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.47/0.64      inference('split', [status(esa)], ['114'])).
% 0.47/0.64  thf('266', plain, (~ ((r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C))),
% 0.47/0.64      inference('sat_resolution*', [status(thm)], ['115', '249'])).
% 0.47/0.64  thf('267', plain, (~ (r2_waybel_7 @ sk_A @ sk_B_1 @ sk_C)),
% 0.47/0.64      inference('simpl_trail', [status(thm)], ['265', '266'])).
% 0.47/0.64  thf('268', plain,
% 0.47/0.64      (((v1_xboole_0 @ sk_B_1)
% 0.47/0.64        | (v2_struct_0 @ sk_A)
% 0.47/0.64        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['264', '267'])).
% 0.47/0.64  thf('269', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('270', plain,
% 0.47/0.64      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.47/0.64      inference('clc', [status(thm)], ['268', '269'])).
% 0.47/0.64  thf('271', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('272', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.47/0.64      inference('clc', [status(thm)], ['270', '271'])).
% 0.47/0.64  thf('273', plain,
% 0.47/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.64      inference('sup+', [status(thm)], ['2', '272'])).
% 0.47/0.64  thf('274', plain,
% 0.47/0.64      ((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['1', '273'])).
% 0.47/0.64  thf('275', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('276', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.47/0.64      inference('demod', [status(thm)], ['274', '275'])).
% 0.47/0.64  thf('277', plain,
% 0.47/0.64      (![X3 : $i]:
% 0.47/0.64         (~ (v1_xboole_0 @ (u1_struct_0 @ X3))
% 0.47/0.64          | ~ (l1_struct_0 @ X3)
% 0.47/0.64          | (v2_struct_0 @ X3))),
% 0.47/0.64      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.47/0.64  thf('278', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.64      inference('sup-', [status(thm)], ['276', '277'])).
% 0.47/0.64  thf('279', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('280', plain, (~ (l1_struct_0 @ sk_A)),
% 0.47/0.64      inference('clc', [status(thm)], ['278', '279'])).
% 0.47/0.64  thf('281', plain, (~ (l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('sup-', [status(thm)], ['0', '280'])).
% 0.47/0.64  thf('282', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('283', plain, ($false), inference('demod', [status(thm)], ['281', '282'])).
% 0.47/0.64  
% 0.47/0.64  % SZS output end Refutation
% 0.47/0.64  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
