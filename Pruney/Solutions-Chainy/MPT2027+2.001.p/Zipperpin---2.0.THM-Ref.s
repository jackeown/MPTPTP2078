%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qrsJgLvvm6

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:30 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 506 expanded)
%              Number of leaves         :   50 ( 169 expanded)
%              Depth                    :   31
%              Number of atoms          : 2657 (12446 expanded)
%              Number of equality atoms :   53 (  53 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k6_waybel_9_type,type,(
    k6_waybel_9: $i > $i > $i > $i > $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k11_yellow_6_type,type,(
    k11_yellow_6: $i > $i > $i )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_waybel_2_type,type,(
    k3_waybel_2: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_yellow_6_type,type,(
    k2_yellow_6: $i > $i > $i > $i > $i )).

thf(dt_l1_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_waybel_9 @ A )
     => ( ( l1_pre_topc @ A )
        & ( l1_orders_2 @ A ) ) ) )).

thf('0',plain,(
    ! [X22: $i] :
      ( ( l1_orders_2 @ X22 )
      | ~ ( l1_waybel_9 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(t26_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_waybel_9 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( v3_yellow_6 @ B @ A )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A )
               => ( r2_hidden @ ( k12_lattice3 @ A @ C @ ( k11_yellow_6 @ A @ B ) ) @ ( k10_yellow_6 @ A @ ( k3_waybel_2 @ A @ C @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( v8_pre_topc @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A )
          & ( l1_waybel_9 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( v3_yellow_6 @ B @ A )
              & ( l1_waybel_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A )
                 => ( r2_hidden @ ( k12_lattice3 @ A @ C @ ( k11_yellow_6 @ A @ B ) ) @ ( k10_yellow_6 @ A @ ( k3_waybel_2 @ A @ C @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_waybel_9])).

thf('2',plain,(
    v3_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k11_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v4_orders_2 @ B )
        & ( v7_waybel_0 @ B )
        & ( v3_yellow_6 @ B @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( m1_subset_1 @ ( k11_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v8_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v7_waybel_0 @ X11 )
      | ~ ( v3_yellow_6 @ X11 @ X10 )
      | ~ ( l1_waybel_0 @ X11 @ X10 )
      | ( m1_subset_1 @ ( k11_yellow_6 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_yellow_6])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X22: $i] :
      ( ( l1_pre_topc @ X22 )
      | ~ ( l1_waybel_9 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6','7','8','9','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X22: $i] :
      ( ( l1_orders_2 @ X22 )
      | ~ ( l1_waybel_9 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k12_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k12_lattice3 @ A @ B @ C )
        = ( k11_lattice3 @ A @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v2_lattice3 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( ( k12_lattice3 @ X7 @ X6 @ X8 )
        = ( k11_lattice3 @ X7 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k12_lattice3])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ sk_A @ sk_C @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ sk_A @ sk_C @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k12_lattice3 @ sk_A @ sk_C @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k12_lattice3 @ sk_A @ sk_C @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k12_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','25'])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('28',plain,(
    ! [X22: $i] :
      ( ( l1_orders_2 @ X22 )
      | ~ ( l1_waybel_9 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_waybel_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ( v1_funct_1 @ ( k4_waybel_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k4_waybel_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( k4_waybel_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( v1_funct_1 @ ( k4_waybel_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('31',plain,
    ( ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X22: $i] :
      ( ( l1_orders_2 @ X22 )
      | ~ ( l1_waybel_9 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( v1_funct_2 @ ( k4_waybel_1 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('38',plain,
    ( ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X22: $i] :
      ( ( l1_orders_2 @ X22 )
      | ~ ( l1_waybel_9 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( m1_subset_1 @ ( k4_waybel_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X20 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X3 @ X1 )
      | ( ( k3_funct_2 @ X1 @ X2 @ X0 @ X3 )
        = ( k1_funct_1 @ X0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','54'])).

thf('56',plain,
    ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('58',plain,(
    ! [X22: $i] :
      ( ( l1_orders_2 @ X22 )
      | ~ ( l1_waybel_9 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(d18_waybel_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ( ( C
                  = ( k4_waybel_1 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( k3_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ C @ D )
                      = ( k11_lattice3 @ A @ B @ D ) ) ) ) ) ) ) )).

thf('62',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( X18
       != ( k4_waybel_1 @ X17 @ X16 ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X17 ) @ X18 @ X19 )
        = ( k11_lattice3 @ X17 @ X16 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( l1_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_waybel_1])).

thf('63',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ X17 @ X16 ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ X17 @ X16 ) @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ ( k4_waybel_1 @ X17 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X17 ) @ ( k4_waybel_1 @ X17 @ X16 ) @ X19 )
        = ( k11_lattice3 @ X17 @ X16 @ X19 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','71'])).

thf('73',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','74'])).

thf('76',plain,
    ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['56','76'])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('80',plain,(
    ! [X22: $i] :
      ( ( l1_orders_2 @ X22 )
      | ~ ( l1_waybel_9 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(redefinition_k2_yellow_6,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_orders_2 @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( u1_struct_0 @ B ) ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k2_yellow_6 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('84',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ X13 )
      | ( ( k2_yellow_6 @ X13 @ X14 @ X12 @ X15 )
        = ( k1_funct_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_yellow_6])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['82','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['80','90'])).

thf('92',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','93'])).

thf('95',plain,
    ( ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X22: $i] :
      ( ( l1_orders_2 @ X22 )
      | ~ ( l1_waybel_9 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( k6_waybel_9 @ A @ A @ ( k4_waybel_1 @ A @ C ) @ B )
                = ( k3_waybel_2 @ A @ C @ B ) ) ) ) ) )).

thf('99',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ( ( k6_waybel_9 @ X24 @ X24 @ ( k4_waybel_1 @ X24 @ X25 ) @ X23 )
        = ( k3_waybel_2 @ X24 @ X25 @ X23 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t18_waybel_9])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k3_waybel_2 @ sk_A @ sk_C @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k3_waybel_2 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k3_waybel_2 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ sk_B )
      = ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['96','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ sk_B )
      = ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(t25_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_waybel_9 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( v3_yellow_6 @ B @ A )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ( ( v5_pre_topc @ C @ A @ A )
               => ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ A ) @ A @ C @ ( k11_yellow_6 @ A @ B ) ) @ ( k10_yellow_6 @ A @ ( k6_waybel_9 @ A @ A @ C @ B ) ) ) ) ) ) ) )).

thf('111',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v7_waybel_0 @ X26 )
      | ~ ( v3_yellow_6 @ X26 @ X27 )
      | ~ ( l1_waybel_0 @ X26 @ X27 )
      | ~ ( v5_pre_topc @ X28 @ X27 @ X27 )
      | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ X27 ) @ X27 @ X28 @ ( k11_yellow_6 @ X27 @ X26 ) ) @ ( k10_yellow_6 @ X27 @ ( k6_waybel_9 @ X27 @ X27 @ X28 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_waybel_9 @ X27 )
      | ~ ( v2_lattice3 @ X27 )
      | ~ ( v1_lattice3 @ X27 )
      | ~ ( v5_orders_2 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ~ ( v3_orders_2 @ X27 )
      | ~ ( v8_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t25_waybel_9])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_waybel_9 @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ X0 ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) ) )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ sk_C ) @ sk_A @ sk_A )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v3_yellow_6 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v5_pre_topc @ ( k4_waybel_1 @ sk_A @ sk_C ) @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ X0 ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v3_yellow_6 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116','117','118','119','120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v3_yellow_6 @ X0 @ sk_A )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ X0 ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ X0 ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v3_yellow_6 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v3_yellow_6 @ X0 @ sk_A )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ X0 ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['108','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ X0 ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v3_yellow_6 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v3_yellow_6 @ sk_B @ sk_A )
    | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['107','126'])).

thf('128',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v3_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['127','128','129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['106','133'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['95','135'])).

thf('137',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ( r2_hidden @ ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['78','137'])).

thf('139',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( ( r2_hidden @ ( k12_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','139'])).

thf('141',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k12_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ~ ( r2_hidden @ ( k12_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['141','142'])).

thf(d1_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( v2_struct_0 @ A )
      <=> ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('144',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_struct_0])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','146'])).

thf('148',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('149',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['147','148'])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('150',plain,(
    ! [X5: $i] :
      ( ~ ( v1_lattice3 @ X5 )
      | ~ ( v2_struct_0 @ X5 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('151',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','153'])).

thf('155',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    $false ),
    inference(demod,[status(thm)],['154','155'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qrsJgLvvm6
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.57  % Solved by: fo/fo7.sh
% 0.35/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.57  % done 154 iterations in 0.115s
% 0.35/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.57  % SZS output start Refutation
% 0.35/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.57  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.35/0.57  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.35/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.57  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.35/0.57  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.35/0.57  thf(k6_waybel_9_type, type, k6_waybel_9: $i > $i > $i > $i > $i).
% 0.35/0.57  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.35/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.57  thf(k11_yellow_6_type, type, k11_yellow_6: $i > $i > $i).
% 0.35/0.57  thf(v3_yellow_6_type, type, v3_yellow_6: $i > $i > $o).
% 0.35/0.57  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 0.35/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.57  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 0.35/0.57  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.35/0.57  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.35/0.57  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.35/0.57  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.35/0.57  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.35/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.35/0.57  thf(k3_waybel_2_type, type, k3_waybel_2: $i > $i > $i > $i).
% 0.35/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.57  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.35/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.57  thf(k12_lattice3_type, type, k12_lattice3: $i > $i > $i > $i).
% 0.35/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.57  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.35/0.57  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.35/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.57  thf(k2_yellow_6_type, type, k2_yellow_6: $i > $i > $i > $i > $i).
% 0.35/0.57  thf(dt_l1_waybel_9, axiom,
% 0.35/0.57    (![A:$i]:
% 0.35/0.57     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 0.35/0.57  thf('0', plain, (![X22 : $i]: ((l1_orders_2 @ X22) | ~ (l1_waybel_9 @ X22))),
% 0.35/0.57      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.35/0.57  thf(dt_l1_pre_topc, axiom,
% 0.35/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.35/0.57  thf('1', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.35/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.57  thf(t26_waybel_9, conjecture,
% 0.35/0.57    (![A:$i]:
% 0.35/0.57     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.35/0.57         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.35/0.57         ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.35/0.57       ( ![B:$i]:
% 0.35/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.35/0.57             ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.35/0.57             ( l1_waybel_0 @ B @ A ) ) =>
% 0.35/0.57           ( ![C:$i]:
% 0.35/0.57             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.57               ( ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) =>
% 0.35/0.57                 ( r2_hidden @
% 0.35/0.57                   ( k12_lattice3 @ A @ C @ ( k11_yellow_6 @ A @ B ) ) @ 
% 0.35/0.57                   ( k10_yellow_6 @ A @ ( k3_waybel_2 @ A @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.35/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.57    (~( ![A:$i]:
% 0.35/0.57        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.35/0.57            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.35/0.57            ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.35/0.57          ( ![B:$i]:
% 0.35/0.57            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.35/0.57                ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.35/0.57                ( l1_waybel_0 @ B @ A ) ) =>
% 0.35/0.57              ( ![C:$i]:
% 0.35/0.57                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.57                  ( ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) =>
% 0.35/0.57                    ( r2_hidden @
% 0.35/0.57                      ( k12_lattice3 @ A @ C @ ( k11_yellow_6 @ A @ B ) ) @ 
% 0.35/0.57                      ( k10_yellow_6 @ A @ ( k3_waybel_2 @ A @ C @ B ) ) ) ) ) ) ) ) ) )),
% 0.35/0.57    inference('cnf.neg', [status(esa)], [t26_waybel_9])).
% 0.35/0.57  thf('2', plain, ((v3_yellow_6 @ sk_B @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(dt_k11_yellow_6, axiom,
% 0.35/0.57    (![A:$i,B:$i]:
% 0.35/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.35/0.57         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.35/0.57         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.35/0.57         ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.35/0.57         ( l1_waybel_0 @ B @ A ) ) =>
% 0.35/0.57       ( m1_subset_1 @ ( k11_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.35/0.57  thf('3', plain,
% 0.35/0.57      (![X10 : $i, X11 : $i]:
% 0.35/0.57         (~ (l1_pre_topc @ X10)
% 0.35/0.57          | ~ (v8_pre_topc @ X10)
% 0.35/0.57          | ~ (v2_pre_topc @ X10)
% 0.35/0.57          | (v2_struct_0 @ X10)
% 0.35/0.57          | (v2_struct_0 @ X11)
% 0.35/0.57          | ~ (v4_orders_2 @ X11)
% 0.35/0.57          | ~ (v7_waybel_0 @ X11)
% 0.35/0.57          | ~ (v3_yellow_6 @ X11 @ X10)
% 0.35/0.57          | ~ (l1_waybel_0 @ X11 @ X10)
% 0.35/0.57          | (m1_subset_1 @ (k11_yellow_6 @ X10 @ X11) @ (u1_struct_0 @ X10)))),
% 0.35/0.57      inference('cnf', [status(esa)], [dt_k11_yellow_6])).
% 0.35/0.57  thf('4', plain,
% 0.35/0.57      (((m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.35/0.57        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.35/0.57        | ~ (v7_waybel_0 @ sk_B)
% 0.35/0.57        | ~ (v4_orders_2 @ sk_B)
% 0.35/0.57        | (v2_struct_0 @ sk_B)
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.57        | ~ (v8_pre_topc @ sk_A)
% 0.35/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.57  thf('5', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('6', plain, ((v7_waybel_0 @ sk_B)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('7', plain, ((v4_orders_2 @ sk_B)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('9', plain, ((v8_pre_topc @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('10', plain, ((l1_waybel_9 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('11', plain,
% 0.35/0.57      (![X22 : $i]: ((l1_pre_topc @ X22) | ~ (l1_waybel_9 @ X22))),
% 0.35/0.57      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.35/0.57  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.57  thf('13', plain,
% 0.35/0.57      (((m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.35/0.57        | (v2_struct_0 @ sk_B)
% 0.35/0.57        | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('demod', [status(thm)], ['4', '5', '6', '7', '8', '9', '12'])).
% 0.35/0.57  thf('14', plain, (~ (v2_struct_0 @ sk_B)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('15', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | (m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('clc', [status(thm)], ['13', '14'])).
% 0.35/0.57  thf('16', plain,
% 0.35/0.57      (![X22 : $i]: ((l1_orders_2 @ X22) | ~ (l1_waybel_9 @ X22))),
% 0.35/0.57      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.35/0.57  thf('17', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(redefinition_k12_lattice3, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.35/0.57         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.35/0.57         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.57       ( ( k12_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ B @ C ) ) ))).
% 0.35/0.57  thf('18', plain,
% 0.35/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.35/0.57          | ~ (l1_orders_2 @ X7)
% 0.35/0.57          | ~ (v2_lattice3 @ X7)
% 0.35/0.57          | ~ (v5_orders_2 @ X7)
% 0.35/0.57          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.35/0.57          | ((k12_lattice3 @ X7 @ X6 @ X8) = (k11_lattice3 @ X7 @ X6 @ X8)))),
% 0.35/0.57      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 0.35/0.57  thf('19', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (((k12_lattice3 @ sk_A @ sk_C @ X0)
% 0.35/0.57            = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (v5_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v2_lattice3 @ sk_A)
% 0.35/0.57          | ~ (l1_orders_2 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.35/0.57  thf('20', plain, ((v5_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('21', plain, ((v2_lattice3 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('22', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (((k12_lattice3 @ sk_A @ sk_C @ X0)
% 0.35/0.57            = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (l1_orders_2 @ sk_A))),
% 0.35/0.57      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.35/0.57  thf('23', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (l1_waybel_9 @ sk_A)
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ((k12_lattice3 @ sk_A @ sk_C @ X0)
% 0.35/0.57              = (k11_lattice3 @ sk_A @ sk_C @ X0)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['16', '22'])).
% 0.35/0.57  thf('24', plain, ((l1_waybel_9 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('25', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ((k12_lattice3 @ sk_A @ sk_C @ X0)
% 0.35/0.57              = (k11_lattice3 @ sk_A @ sk_C @ X0)))),
% 0.35/0.57      inference('demod', [status(thm)], ['23', '24'])).
% 0.35/0.57  thf('26', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | ((k12_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.35/0.57            = (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['15', '25'])).
% 0.35/0.57  thf('27', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | (m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('clc', [status(thm)], ['13', '14'])).
% 0.35/0.57  thf('28', plain,
% 0.35/0.57      (![X22 : $i]: ((l1_orders_2 @ X22) | ~ (l1_waybel_9 @ X22))),
% 0.35/0.57      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.35/0.57  thf('29', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(dt_k4_waybel_1, axiom,
% 0.35/0.57    (![A:$i,B:$i]:
% 0.35/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.35/0.57         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.57       ( ( v1_funct_1 @ ( k4_waybel_1 @ A @ B ) ) & 
% 0.35/0.57         ( v1_funct_2 @
% 0.35/0.57           ( k4_waybel_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.35/0.57         ( m1_subset_1 @
% 0.35/0.57           ( k4_waybel_1 @ A @ B ) @ 
% 0.35/0.57           ( k1_zfmisc_1 @
% 0.35/0.57             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.35/0.57  thf('30', plain,
% 0.35/0.57      (![X20 : $i, X21 : $i]:
% 0.35/0.57         (~ (l1_orders_2 @ X20)
% 0.35/0.57          | (v2_struct_0 @ X20)
% 0.35/0.57          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.35/0.57          | (v1_funct_1 @ (k4_waybel_1 @ X20 @ X21)))),
% 0.35/0.57      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.35/0.57  thf('31', plain,
% 0.35/0.57      (((v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | ~ (l1_orders_2 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.35/0.57  thf('32', plain,
% 0.35/0.57      ((~ (l1_waybel_9 @ sk_A)
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['28', '31'])).
% 0.35/0.57  thf('33', plain, ((l1_waybel_9 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('34', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.35/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.35/0.57  thf('35', plain,
% 0.35/0.57      (![X22 : $i]: ((l1_orders_2 @ X22) | ~ (l1_waybel_9 @ X22))),
% 0.35/0.57      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.35/0.57  thf('36', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('37', plain,
% 0.35/0.57      (![X20 : $i, X21 : $i]:
% 0.35/0.57         (~ (l1_orders_2 @ X20)
% 0.35/0.57          | (v2_struct_0 @ X20)
% 0.35/0.57          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.35/0.57          | (v1_funct_2 @ (k4_waybel_1 @ X20 @ X21) @ (u1_struct_0 @ X20) @ 
% 0.35/0.57             (u1_struct_0 @ X20)))),
% 0.35/0.57      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.35/0.57  thf('38', plain,
% 0.35/0.57      (((v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57         (u1_struct_0 @ sk_A))
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | ~ (l1_orders_2 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.35/0.57  thf('39', plain,
% 0.35/0.57      ((~ (l1_waybel_9 @ sk_A)
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57           (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['35', '38'])).
% 0.35/0.57  thf('40', plain, ((l1_waybel_9 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('41', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57           (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.35/0.57  thf('42', plain,
% 0.35/0.57      (![X22 : $i]: ((l1_orders_2 @ X22) | ~ (l1_waybel_9 @ X22))),
% 0.35/0.57      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.35/0.57  thf('43', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('44', plain,
% 0.35/0.57      (![X20 : $i, X21 : $i]:
% 0.35/0.57         (~ (l1_orders_2 @ X20)
% 0.35/0.57          | (v2_struct_0 @ X20)
% 0.35/0.57          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.35/0.57          | (m1_subset_1 @ (k4_waybel_1 @ X20 @ X21) @ 
% 0.35/0.57             (k1_zfmisc_1 @ 
% 0.35/0.57              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X20)))))),
% 0.35/0.57      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.35/0.57  thf('45', plain,
% 0.35/0.57      (((m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57         (k1_zfmisc_1 @ 
% 0.35/0.57          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | ~ (l1_orders_2 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.35/0.57  thf('46', plain,
% 0.35/0.57      ((~ (l1_waybel_9 @ sk_A)
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57           (k1_zfmisc_1 @ 
% 0.35/0.57            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['42', '45'])).
% 0.35/0.57  thf('47', plain, ((l1_waybel_9 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('48', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57           (k1_zfmisc_1 @ 
% 0.35/0.57            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.57      inference('demod', [status(thm)], ['46', '47'])).
% 0.35/0.57  thf(redefinition_k3_funct_2, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.35/0.57         ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.35/0.57         ( m1_subset_1 @ D @ A ) ) =>
% 0.35/0.57       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.35/0.57  thf('49', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.35/0.57          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.35/0.57          | ~ (v1_funct_1 @ X0)
% 0.35/0.57          | (v1_xboole_0 @ X1)
% 0.35/0.57          | ~ (m1_subset_1 @ X3 @ X1)
% 0.35/0.57          | ((k3_funct_2 @ X1 @ X2 @ X0 @ X3) = (k1_funct_1 @ X0 @ X3)))),
% 0.35/0.57      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.35/0.57  thf('50', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.35/0.57          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.35/0.57  thf('51', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.35/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['41', '50'])).
% 0.35/0.57  thf('52', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57            (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57            = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('simplify', [status(thm)], ['51'])).
% 0.35/0.57  thf('53', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | (v2_struct_0 @ sk_A)
% 0.35/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['34', '52'])).
% 0.35/0.57  thf('54', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57            (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57            = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('simplify', [status(thm)], ['53'])).
% 0.35/0.57  thf('55', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57        | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.35/0.57            = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57               (k11_yellow_6 @ sk_A @ sk_B))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['27', '54'])).
% 0.35/0.57  thf('56', plain,
% 0.35/0.57      ((((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.35/0.57          = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57             (k11_yellow_6 @ sk_A @ sk_B)))
% 0.35/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57        | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('simplify', [status(thm)], ['55'])).
% 0.35/0.57  thf('57', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | (m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('clc', [status(thm)], ['13', '14'])).
% 0.35/0.57  thf('58', plain,
% 0.35/0.57      (![X22 : $i]: ((l1_orders_2 @ X22) | ~ (l1_waybel_9 @ X22))),
% 0.35/0.57      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.35/0.57  thf('59', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.35/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.35/0.57  thf('60', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57           (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.35/0.57  thf('61', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57           (k1_zfmisc_1 @ 
% 0.35/0.57            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.57      inference('demod', [status(thm)], ['46', '47'])).
% 0.35/0.57  thf(d18_waybel_1, axiom,
% 0.35/0.57    (![A:$i]:
% 0.35/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.57       ( ![B:$i]:
% 0.35/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.57           ( ![C:$i]:
% 0.35/0.57             ( ( ( v1_funct_1 @ C ) & 
% 0.35/0.57                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.35/0.57                 ( m1_subset_1 @
% 0.35/0.57                   C @ 
% 0.35/0.57                   ( k1_zfmisc_1 @
% 0.35/0.57                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.35/0.57               ( ( ( C ) = ( k4_waybel_1 @ A @ B ) ) <=>
% 0.35/0.57                 ( ![D:$i]:
% 0.35/0.57                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.57                     ( ( k3_funct_2 @
% 0.35/0.57                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ C @ D ) =
% 0.35/0.57                       ( k11_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.57  thf('62', plain,
% 0.35/0.57      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.35/0.57          | ((X18) != (k4_waybel_1 @ X17 @ X16))
% 0.35/0.57          | ((k3_funct_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X17) @ X18 @ 
% 0.35/0.57              X19) = (k11_lattice3 @ X17 @ X16 @ X19))
% 0.35/0.57          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.35/0.57          | ~ (m1_subset_1 @ X18 @ 
% 0.35/0.57               (k1_zfmisc_1 @ 
% 0.35/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X17))))
% 0.35/0.57          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X17))
% 0.35/0.57          | ~ (v1_funct_1 @ X18)
% 0.35/0.57          | ~ (l1_orders_2 @ X17)
% 0.35/0.57          | (v2_struct_0 @ X17))),
% 0.35/0.57      inference('cnf', [status(esa)], [d18_waybel_1])).
% 0.35/0.57  thf('63', plain,
% 0.35/0.57      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.35/0.57         ((v2_struct_0 @ X17)
% 0.35/0.57          | ~ (l1_orders_2 @ X17)
% 0.35/0.57          | ~ (v1_funct_1 @ (k4_waybel_1 @ X17 @ X16))
% 0.35/0.57          | ~ (v1_funct_2 @ (k4_waybel_1 @ X17 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.35/0.57               (u1_struct_0 @ X17))
% 0.35/0.57          | ~ (m1_subset_1 @ (k4_waybel_1 @ X17 @ X16) @ 
% 0.35/0.57               (k1_zfmisc_1 @ 
% 0.35/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X17))))
% 0.35/0.57          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.35/0.57          | ((k3_funct_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X17) @ 
% 0.35/0.57              (k4_waybel_1 @ X17 @ X16) @ X19)
% 0.35/0.57              = (k11_lattice3 @ X17 @ X16 @ X19))
% 0.35/0.57          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17)))),
% 0.35/0.57      inference('simplify', [status(thm)], ['62'])).
% 0.35/0.57  thf('64', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.35/0.57          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['61', '63'])).
% 0.35/0.57  thf('65', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('66', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.35/0.57          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('demod', [status(thm)], ['64', '65'])).
% 0.35/0.57  thf('67', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (l1_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.35/0.57          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('simplify', [status(thm)], ['66'])).
% 0.35/0.57  thf('68', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | (v2_struct_0 @ sk_A)
% 0.35/0.57          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.35/0.57          | ~ (l1_orders_2 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['60', '67'])).
% 0.35/0.57  thf('69', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (l1_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('simplify', [status(thm)], ['68'])).
% 0.35/0.57  thf('70', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | (v2_struct_0 @ sk_A)
% 0.35/0.57          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (l1_orders_2 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['59', '69'])).
% 0.35/0.57  thf('71', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (l1_orders_2 @ sk_A)
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('simplify', [status(thm)], ['70'])).
% 0.35/0.57  thf('72', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (l1_waybel_9 @ sk_A)
% 0.35/0.57          | (v2_struct_0 @ sk_A)
% 0.35/0.57          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['58', '71'])).
% 0.35/0.57  thf('73', plain, ((l1_waybel_9 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('74', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('demod', [status(thm)], ['72', '73'])).
% 0.35/0.57  thf('75', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.35/0.57            = (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)))
% 0.35/0.57        | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['57', '74'])).
% 0.35/0.57  thf('76', plain,
% 0.35/0.57      ((((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.35/0.57          = (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)))
% 0.35/0.57        | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('simplify', [status(thm)], ['75'])).
% 0.35/0.57  thf('77', plain,
% 0.35/0.57      ((((k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57          (k11_yellow_6 @ sk_A @ sk_B))
% 0.35/0.57          = (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)))
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57        | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('sup+', [status(thm)], ['56', '76'])).
% 0.35/0.57  thf('78', plain,
% 0.35/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | ((k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57            (k11_yellow_6 @ sk_A @ sk_B))
% 0.35/0.57            = (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B))))),
% 0.35/0.57      inference('simplify', [status(thm)], ['77'])).
% 0.35/0.57  thf('79', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | (m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('clc', [status(thm)], ['13', '14'])).
% 0.35/0.57  thf('80', plain,
% 0.35/0.57      (![X22 : $i]: ((l1_orders_2 @ X22) | ~ (l1_waybel_9 @ X22))),
% 0.35/0.57      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.35/0.57  thf('81', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.35/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.35/0.57  thf('82', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57           (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.35/0.57  thf('83', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57           (k1_zfmisc_1 @ 
% 0.35/0.57            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.57      inference('demod', [status(thm)], ['46', '47'])).
% 0.35/0.57  thf(redefinition_k2_yellow_6, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.35/0.57         ( l1_orders_2 @ B ) & ( v1_funct_1 @ C ) & 
% 0.35/0.57         ( v1_funct_2 @ C @ A @ ( u1_struct_0 @ B ) ) & 
% 0.35/0.57         ( m1_subset_1 @
% 0.35/0.57           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.35/0.57         ( m1_subset_1 @ D @ A ) ) =>
% 0.35/0.57       ( ( k2_yellow_6 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.35/0.57  thf('84', plain,
% 0.35/0.57      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.35/0.57         (~ (m1_subset_1 @ X12 @ 
% 0.35/0.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ (u1_struct_0 @ X14))))
% 0.35/0.57          | ~ (v1_funct_2 @ X12 @ X13 @ (u1_struct_0 @ X14))
% 0.35/0.57          | ~ (v1_funct_1 @ X12)
% 0.35/0.57          | ~ (l1_orders_2 @ X14)
% 0.35/0.57          | (v2_struct_0 @ X14)
% 0.35/0.57          | (v1_xboole_0 @ X13)
% 0.35/0.57          | ~ (m1_subset_1 @ X15 @ X13)
% 0.35/0.57          | ((k2_yellow_6 @ X13 @ X14 @ X12 @ X15) = (k1_funct_1 @ X12 @ X15)))),
% 0.35/0.57      inference('cnf', [status(esa)], [redefinition_k2_yellow_6])).
% 0.35/0.57  thf('85', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (v2_struct_0 @ sk_A)
% 0.35/0.57          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.35/0.57          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['83', '84'])).
% 0.35/0.57  thf('86', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57             (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.35/0.57          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('simplify', [status(thm)], ['85'])).
% 0.35/0.57  thf('87', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | (v2_struct_0 @ sk_A)
% 0.35/0.57          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['82', '86'])).
% 0.35/0.57  thf('88', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.35/0.57          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('simplify', [status(thm)], ['87'])).
% 0.35/0.57  thf('89', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | (v2_struct_0 @ sk_A)
% 0.35/0.57          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (l1_orders_2 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['81', '88'])).
% 0.35/0.57  thf('90', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (l1_orders_2 @ sk_A)
% 0.35/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('simplify', [status(thm)], ['89'])).
% 0.35/0.57  thf('91', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (l1_waybel_9 @ sk_A)
% 0.35/0.57          | (v2_struct_0 @ sk_A)
% 0.35/0.57          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['80', '90'])).
% 0.35/0.57  thf('92', plain, ((l1_waybel_9 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('93', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.35/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('demod', [status(thm)], ['91', '92'])).
% 0.35/0.57  thf('94', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57        | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.35/0.57            = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57               (k11_yellow_6 @ sk_A @ sk_B)))
% 0.35/0.57        | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['79', '93'])).
% 0.35/0.57  thf('95', plain,
% 0.35/0.57      ((((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.35/0.57          = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57             (k11_yellow_6 @ sk_A @ sk_B)))
% 0.35/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57        | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('simplify', [status(thm)], ['94'])).
% 0.35/0.57  thf('96', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('97', plain,
% 0.35/0.57      (![X22 : $i]: ((l1_orders_2 @ X22) | ~ (l1_waybel_9 @ X22))),
% 0.35/0.57      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.35/0.57  thf('98', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf(t18_waybel_9, axiom,
% 0.35/0.57    (![A:$i]:
% 0.35/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.57       ( ![B:$i]:
% 0.35/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.35/0.57           ( ![C:$i]:
% 0.35/0.57             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.57               ( ( k6_waybel_9 @ A @ A @ ( k4_waybel_1 @ A @ C ) @ B ) =
% 0.35/0.57                 ( k3_waybel_2 @ A @ C @ B ) ) ) ) ) ) ))).
% 0.35/0.57  thf('99', plain,
% 0.35/0.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.35/0.57         ((v2_struct_0 @ X23)
% 0.35/0.57          | ~ (l1_waybel_0 @ X23 @ X24)
% 0.35/0.57          | ((k6_waybel_9 @ X24 @ X24 @ (k4_waybel_1 @ X24 @ X25) @ X23)
% 0.35/0.57              = (k3_waybel_2 @ X24 @ X25 @ X23))
% 0.35/0.57          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.35/0.57          | ~ (l1_orders_2 @ X24)
% 0.35/0.57          | (v2_struct_0 @ X24))),
% 0.35/0.57      inference('cnf', [status(esa)], [t18_waybel_9])).
% 0.35/0.57  thf('100', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.57          | ((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k3_waybel_2 @ sk_A @ sk_C @ X0))
% 0.35/0.57          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.35/0.57          | (v2_struct_0 @ X0))),
% 0.35/0.57      inference('sup-', [status(thm)], ['98', '99'])).
% 0.35/0.57  thf('101', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (l1_waybel_9 @ sk_A)
% 0.35/0.57          | (v2_struct_0 @ X0)
% 0.35/0.57          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.35/0.57          | ((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k3_waybel_2 @ sk_A @ sk_C @ X0))
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['97', '100'])).
% 0.35/0.57  thf('102', plain, ((l1_waybel_9 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('103', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ X0)
% 0.35/0.57          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.35/0.57          | ((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.35/0.57              = (k3_waybel_2 @ sk_A @ sk_C @ X0))
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('demod', [status(thm)], ['101', '102'])).
% 0.35/0.57  thf('104', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | ((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B)
% 0.35/0.57            = (k3_waybel_2 @ sk_A @ sk_C @ sk_B))
% 0.35/0.57        | (v2_struct_0 @ sk_B))),
% 0.35/0.57      inference('sup-', [status(thm)], ['96', '103'])).
% 0.35/0.57  thf('105', plain, (~ (v2_struct_0 @ sk_B)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('106', plain,
% 0.35/0.57      ((((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B)
% 0.35/0.57          = (k3_waybel_2 @ sk_A @ sk_C @ sk_B))
% 0.35/0.57        | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('clc', [status(thm)], ['104', '105'])).
% 0.35/0.57  thf('107', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('108', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.35/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.35/0.57  thf('109', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.57           (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.35/0.57  thf('110', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57           (k1_zfmisc_1 @ 
% 0.35/0.57            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.57      inference('demod', [status(thm)], ['46', '47'])).
% 0.35/0.57  thf(t25_waybel_9, axiom,
% 0.35/0.57    (![A:$i]:
% 0.35/0.57     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.35/0.57         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.35/0.57         ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.35/0.57       ( ![B:$i]:
% 0.35/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.35/0.57             ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.35/0.57             ( l1_waybel_0 @ B @ A ) ) =>
% 0.35/0.57           ( ![C:$i]:
% 0.35/0.57             ( ( ( v1_funct_1 @ C ) & 
% 0.35/0.57                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.35/0.57                 ( m1_subset_1 @
% 0.35/0.57                   C @ 
% 0.35/0.57                   ( k1_zfmisc_1 @
% 0.35/0.57                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.35/0.57               ( ( v5_pre_topc @ C @ A @ A ) =>
% 0.35/0.57                 ( r2_hidden @
% 0.35/0.57                   ( k2_yellow_6 @
% 0.35/0.57                     ( u1_struct_0 @ A ) @ A @ C @ ( k11_yellow_6 @ A @ B ) ) @ 
% 0.35/0.57                   ( k10_yellow_6 @ A @ ( k6_waybel_9 @ A @ A @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.35/0.57  thf('111', plain,
% 0.35/0.57      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.35/0.57         ((v2_struct_0 @ X26)
% 0.35/0.57          | ~ (v4_orders_2 @ X26)
% 0.35/0.57          | ~ (v7_waybel_0 @ X26)
% 0.35/0.57          | ~ (v3_yellow_6 @ X26 @ X27)
% 0.35/0.57          | ~ (l1_waybel_0 @ X26 @ X27)
% 0.35/0.57          | ~ (v5_pre_topc @ X28 @ X27 @ X27)
% 0.35/0.57          | (r2_hidden @ 
% 0.35/0.57             (k2_yellow_6 @ (u1_struct_0 @ X27) @ X27 @ X28 @ 
% 0.35/0.57              (k11_yellow_6 @ X27 @ X26)) @ 
% 0.35/0.57             (k10_yellow_6 @ X27 @ (k6_waybel_9 @ X27 @ X27 @ X28 @ X26)))
% 0.35/0.57          | ~ (m1_subset_1 @ X28 @ 
% 0.35/0.57               (k1_zfmisc_1 @ 
% 0.35/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X27))))
% 0.35/0.57          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X27))
% 0.35/0.57          | ~ (v1_funct_1 @ X28)
% 0.35/0.57          | ~ (l1_waybel_9 @ X27)
% 0.35/0.57          | ~ (v2_lattice3 @ X27)
% 0.35/0.57          | ~ (v1_lattice3 @ X27)
% 0.35/0.57          | ~ (v5_orders_2 @ X27)
% 0.35/0.57          | ~ (v4_orders_2 @ X27)
% 0.35/0.57          | ~ (v3_orders_2 @ X27)
% 0.35/0.57          | ~ (v8_pre_topc @ X27)
% 0.35/0.57          | ~ (v2_pre_topc @ X27))),
% 0.35/0.57      inference('cnf', [status(esa)], [t25_waybel_9])).
% 0.35/0.57  thf('112', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.57          | ~ (v8_pre_topc @ sk_A)
% 0.35/0.57          | ~ (v3_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v4_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v5_orders_2 @ sk_A)
% 0.35/0.57          | ~ (v1_lattice3 @ sk_A)
% 0.35/0.57          | ~ (v2_lattice3 @ sk_A)
% 0.35/0.57          | ~ (l1_waybel_9 @ sk_A)
% 0.35/0.57          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.35/0.57          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (r2_hidden @ 
% 0.35/0.57             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.35/0.57             (k10_yellow_6 @ sk_A @ 
% 0.35/0.57              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.35/0.57          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_A @ sk_A)
% 0.35/0.57          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.35/0.57          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.35/0.57          | ~ (v7_waybel_0 @ X0)
% 0.35/0.57          | ~ (v4_orders_2 @ X0)
% 0.35/0.57          | (v2_struct_0 @ X0))),
% 0.35/0.57      inference('sup-', [status(thm)], ['110', '111'])).
% 0.35/0.57  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('114', plain, ((v8_pre_topc @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('115', plain, ((v3_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('116', plain, ((v4_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('117', plain, ((v5_orders_2 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('118', plain, ((v1_lattice3 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('119', plain, ((v2_lattice3 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('120', plain, ((l1_waybel_9 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('121', plain,
% 0.35/0.57      ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_A @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('122', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.35/0.57          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.35/0.57          | (r2_hidden @ 
% 0.35/0.57             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.35/0.57             (k10_yellow_6 @ sk_A @ 
% 0.35/0.57              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.35/0.57          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.35/0.57          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.35/0.57          | ~ (v7_waybel_0 @ X0)
% 0.35/0.57          | ~ (v4_orders_2 @ X0)
% 0.35/0.57          | (v2_struct_0 @ X0))),
% 0.35/0.57      inference('demod', [status(thm)],
% 0.35/0.57                ['112', '113', '114', '115', '116', '117', '118', '119', 
% 0.35/0.57                 '120', '121'])).
% 0.35/0.57  thf('123', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | (v2_struct_0 @ X0)
% 0.35/0.57          | ~ (v4_orders_2 @ X0)
% 0.35/0.57          | ~ (v7_waybel_0 @ X0)
% 0.35/0.57          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.35/0.57          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.35/0.57          | (r2_hidden @ 
% 0.35/0.57             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.35/0.57             (k10_yellow_6 @ sk_A @ 
% 0.35/0.57              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.35/0.57          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['109', '122'])).
% 0.35/0.57  thf('124', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.35/0.57          | (r2_hidden @ 
% 0.35/0.57             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.35/0.57             (k10_yellow_6 @ sk_A @ 
% 0.35/0.57              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.35/0.57          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.35/0.57          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.35/0.57          | ~ (v7_waybel_0 @ X0)
% 0.35/0.57          | ~ (v4_orders_2 @ X0)
% 0.35/0.57          | (v2_struct_0 @ X0)
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('simplify', [status(thm)], ['123'])).
% 0.35/0.57  thf('125', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((v2_struct_0 @ sk_A)
% 0.35/0.57          | (v2_struct_0 @ sk_A)
% 0.35/0.57          | (v2_struct_0 @ X0)
% 0.35/0.57          | ~ (v4_orders_2 @ X0)
% 0.35/0.57          | ~ (v7_waybel_0 @ X0)
% 0.35/0.57          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.35/0.57          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.35/0.57          | (r2_hidden @ 
% 0.35/0.57             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.35/0.57             (k10_yellow_6 @ sk_A @ 
% 0.35/0.57              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['108', '124'])).
% 0.35/0.57  thf('126', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((r2_hidden @ 
% 0.35/0.57           (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.35/0.57           (k10_yellow_6 @ sk_A @ 
% 0.35/0.57            (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.35/0.57          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.35/0.57          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.35/0.57          | ~ (v7_waybel_0 @ X0)
% 0.35/0.57          | ~ (v4_orders_2 @ X0)
% 0.35/0.57          | (v2_struct_0 @ X0)
% 0.35/0.57          | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('simplify', [status(thm)], ['125'])).
% 0.35/0.57  thf('127', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | (v2_struct_0 @ sk_B)
% 0.35/0.57        | ~ (v4_orders_2 @ sk_B)
% 0.35/0.57        | ~ (v7_waybel_0 @ sk_B)
% 0.35/0.57        | ~ (v3_yellow_6 @ sk_B @ sk_A)
% 0.35/0.57        | (r2_hidden @ 
% 0.35/0.57           (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.35/0.57           (k10_yellow_6 @ sk_A @ 
% 0.35/0.57            (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['107', '126'])).
% 0.35/0.57  thf('128', plain, ((v4_orders_2 @ sk_B)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('129', plain, ((v7_waybel_0 @ sk_B)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('130', plain, ((v3_yellow_6 @ sk_B @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('131', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | (v2_struct_0 @ sk_B)
% 0.35/0.57        | (r2_hidden @ 
% 0.35/0.57           (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.35/0.57           (k10_yellow_6 @ sk_A @ 
% 0.35/0.57            (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B))))),
% 0.35/0.57      inference('demod', [status(thm)], ['127', '128', '129', '130'])).
% 0.35/0.57  thf('132', plain, (~ (v2_struct_0 @ sk_B)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('133', plain,
% 0.35/0.57      (((r2_hidden @ 
% 0.35/0.57         (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.35/0.57         (k10_yellow_6 @ sk_A @ 
% 0.35/0.57          (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B)))
% 0.35/0.57        | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('clc', [status(thm)], ['131', '132'])).
% 0.35/0.57  thf('134', plain,
% 0.35/0.57      (((r2_hidden @ 
% 0.35/0.57         (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.35/0.57         (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('sup+', [status(thm)], ['106', '133'])).
% 0.35/0.57  thf('135', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A)
% 0.35/0.57        | (r2_hidden @ 
% 0.35/0.57           (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.35/0.57            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.35/0.57           (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B))))),
% 0.35/0.57      inference('simplify', [status(thm)], ['134'])).
% 0.35/0.57  thf('136', plain,
% 0.35/0.57      (((r2_hidden @ 
% 0.35/0.57         (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57          (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.35/0.57         (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57        | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('sup+', [status(thm)], ['95', '135'])).
% 0.35/0.57  thf('137', plain,
% 0.35/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | (r2_hidden @ 
% 0.35/0.57           (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.35/0.57            (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.35/0.57           (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B))))),
% 0.35/0.57      inference('simplify', [status(thm)], ['136'])).
% 0.35/0.57  thf('138', plain,
% 0.35/0.57      (((r2_hidden @ 
% 0.35/0.57         (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.35/0.57         (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('sup+', [status(thm)], ['78', '137'])).
% 0.35/0.57  thf('139', plain,
% 0.35/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | (r2_hidden @ 
% 0.35/0.57           (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.35/0.57           (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B))))),
% 0.35/0.57      inference('simplify', [status(thm)], ['138'])).
% 0.35/0.57  thf('140', plain,
% 0.35/0.57      (((r2_hidden @ 
% 0.35/0.57         (k12_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.35/0.57         (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('sup+', [status(thm)], ['26', '139'])).
% 0.35/0.57  thf('141', plain,
% 0.35/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.57        | (v2_struct_0 @ sk_A)
% 0.35/0.57        | (r2_hidden @ 
% 0.35/0.57           (k12_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.35/0.57           (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B))))),
% 0.35/0.57      inference('simplify', [status(thm)], ['140'])).
% 0.35/0.57  thf('142', plain,
% 0.35/0.57      (~ (r2_hidden @ 
% 0.35/0.57          (k12_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.35/0.57          (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('143', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.57      inference('clc', [status(thm)], ['141', '142'])).
% 0.35/0.57  thf(d1_struct_0, axiom,
% 0.35/0.57    (![A:$i]:
% 0.35/0.57     ( ( l1_struct_0 @ A ) =>
% 0.35/0.57       ( ( v2_struct_0 @ A ) <=> ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.35/0.57  thf('144', plain,
% 0.35/0.57      (![X9 : $i]:
% 0.35/0.57         (~ (v1_xboole_0 @ (u1_struct_0 @ X9))
% 0.35/0.57          | (v2_struct_0 @ X9)
% 0.35/0.57          | ~ (l1_struct_0 @ X9))),
% 0.35/0.57      inference('cnf', [status(esa)], [d1_struct_0])).
% 0.35/0.57  thf('145', plain,
% 0.35/0.57      (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['143', '144'])).
% 0.35/0.57  thf('146', plain, ((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('simplify', [status(thm)], ['145'])).
% 0.35/0.57  thf('147', plain, ((~ (l1_pre_topc @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['1', '146'])).
% 0.35/0.57  thf('148', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.57  thf('149', plain, ((v2_struct_0 @ sk_A)),
% 0.35/0.57      inference('demod', [status(thm)], ['147', '148'])).
% 0.35/0.57  thf(cc1_lattice3, axiom,
% 0.35/0.57    (![A:$i]:
% 0.35/0.57     ( ( l1_orders_2 @ A ) =>
% 0.35/0.57       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.35/0.57  thf('150', plain,
% 0.35/0.57      (![X5 : $i]:
% 0.35/0.57         (~ (v1_lattice3 @ X5) | ~ (v2_struct_0 @ X5) | ~ (l1_orders_2 @ X5))),
% 0.35/0.57      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.35/0.57  thf('151', plain, ((~ (l1_orders_2 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 0.35/0.57      inference('sup-', [status(thm)], ['149', '150'])).
% 0.35/0.57  thf('152', plain, ((v1_lattice3 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('153', plain, (~ (l1_orders_2 @ sk_A)),
% 0.35/0.57      inference('demod', [status(thm)], ['151', '152'])).
% 0.35/0.57  thf('154', plain, (~ (l1_waybel_9 @ sk_A)),
% 0.35/0.57      inference('sup-', [status(thm)], ['0', '153'])).
% 0.35/0.57  thf('155', plain, ((l1_waybel_9 @ sk_A)),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.57  thf('156', plain, ($false), inference('demod', [status(thm)], ['154', '155'])).
% 0.35/0.57  
% 0.35/0.57  % SZS output end Refutation
% 0.35/0.57  
% 0.35/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
