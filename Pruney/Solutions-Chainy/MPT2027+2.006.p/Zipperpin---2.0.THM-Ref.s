%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bvgalsxsp3

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 506 expanded)
%              Number of leaves         :   50 ( 169 expanded)
%              Depth                    :   30
%              Number of atoms          : 2655 (12444 expanded)
%              Number of equality atoms :   53 (  53 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k6_waybel_9_type,type,(
    k6_waybel_9: $i > $i > $i > $i > $i )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k11_yellow_6_type,type,(
    k11_yellow_6: $i > $i > $i )).

thf(k2_yellow_6_type,type,(
    k2_yellow_6: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(k3_waybel_2_type,type,(
    k3_waybel_2: $i > $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

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

thf('1',plain,(
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

thf('2',plain,(
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

thf('3',plain,
    ( ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X22: $i] :
      ( ( l1_pre_topc @ X22 )
      | ~ ( l1_waybel_9 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5','6','7','8','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X22: $i] :
      ( ( l1_orders_2 @ X22 )
      | ~ ( l1_waybel_9 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v2_lattice3 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( ( k12_lattice3 @ X8 @ X7 @ X9 )
        = ( k11_lattice3 @ X8 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k12_lattice3])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ sk_A @ sk_C @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ sk_A @ sk_C @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k12_lattice3 @ sk_A @ sk_C @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k12_lattice3 @ sk_A @ sk_C @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k12_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','24'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('27',plain,(
    ! [X22: $i] :
      ( ( l1_orders_2 @ X22 )
      | ~ ( l1_waybel_9 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( v1_funct_1 @ ( k4_waybel_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('30',plain,
    ( ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X22: $i] :
      ( ( l1_orders_2 @ X22 )
      | ~ ( l1_waybel_9 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( v1_funct_2 @ ( k4_waybel_1 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('37',plain,
    ( ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X22: $i] :
      ( ( l1_orders_2 @ X22 )
      | ~ ( l1_waybel_9 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( m1_subset_1 @ ( k4_waybel_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X20 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('44',plain,
    ( ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X3 @ X1 )
      | ( ( k3_funct_2 @ X1 @ X2 @ X0 @ X3 )
        = ( k1_funct_1 @ X0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','53'])).

thf('55',plain,
    ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('57',plain,(
    ! [X22: $i] :
      ( ( l1_orders_2 @ X22 )
      | ~ ( l1_waybel_9 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

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

thf('61',plain,(
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

thf('62',plain,(
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
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
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
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','70'])).

thf('72',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','73'])).

thf('75',plain,
    ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['55','75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('79',plain,(
    ! [X22: $i] :
      ( ( l1_orders_2 @ X22 )
      | ~ ( l1_waybel_9 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

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

thf('83',plain,(
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

thf('84',plain,(
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
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['81','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','89'])).

thf('91',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','92'])).

thf('94',plain,
    ( ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X22: $i] :
      ( ( l1_orders_2 @ X22 )
      | ~ ( l1_waybel_9 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('97',plain,(
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

thf('98',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ( ( k6_waybel_9 @ X24 @ X24 @ ( k4_waybel_1 @ X24 @ X25 ) @ X23 )
        = ( k3_waybel_2 @ X24 @ X25 @ X23 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t18_waybel_9])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k3_waybel_2 @ sk_A @ sk_C @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k3_waybel_2 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k3_waybel_2 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ sk_B )
      = ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['95','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ sk_B )
      = ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

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

thf('110',plain,(
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

thf('111',plain,(
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
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v5_pre_topc @ ( k4_waybel_1 @ sk_A @ sk_C ) @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
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
    inference(demod,[status(thm)],['111','112','113','114','115','116','117','118','119','120'])).

thf('122',plain,(
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
    inference('sup-',[status(thm)],['108','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ X0 ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v3_yellow_6 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v3_yellow_6 @ X0 @ sk_A )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ X0 ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['107','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ X0 ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v3_yellow_6 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v3_yellow_6 @ sk_B @ sk_A )
    | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['106','125'])).

thf('127',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v3_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['105','132'])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['94','134'])).

thf('136',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( r2_hidden @ ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['77','136'])).

thf('138',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( r2_hidden @ ( k12_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','138'])).

thf('140',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k12_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ~ ( r2_hidden @ ( k12_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('143',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('146',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('147',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['144','147'])).

thf('149',plain,(
    v2_struct_0 @ sk_A ),
    inference(simplify,[status(thm)],['148'])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('150',plain,(
    ! [X6: $i] :
      ( ~ ( v2_lattice3 @ X6 )
      | ~ ( v2_struct_0 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

thf('151',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v2_lattice3 @ sk_A ),
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
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bvgalsxsp3
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.60  % Solved by: fo/fo7.sh
% 0.21/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.60  % done 153 iterations in 0.143s
% 0.21/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.60  % SZS output start Refutation
% 0.21/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.60  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 0.21/0.60  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.60  thf(k6_waybel_9_type, type, k6_waybel_9: $i > $i > $i > $i > $i).
% 0.21/0.60  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.21/0.60  thf(v3_yellow_6_type, type, v3_yellow_6: $i > $i > $o).
% 0.21/0.60  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.21/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.60  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.60  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.60  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.60  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.60  thf(k11_yellow_6_type, type, k11_yellow_6: $i > $i > $i).
% 0.21/0.60  thf(k2_yellow_6_type, type, k2_yellow_6: $i > $i > $i > $i > $i).
% 0.21/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.60  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 0.21/0.60  thf(k3_waybel_2_type, type, k3_waybel_2: $i > $i > $i > $i).
% 0.21/0.60  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.60  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.21/0.60  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.21/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.60  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.21/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.60  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.21/0.60  thf(k12_lattice3_type, type, k12_lattice3: $i > $i > $i > $i).
% 0.21/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.60  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.60  thf(dt_l1_waybel_9, axiom,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 0.21/0.60  thf('0', plain, (![X22 : $i]: ((l1_orders_2 @ X22) | ~ (l1_waybel_9 @ X22))),
% 0.21/0.60      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.21/0.60  thf(t26_waybel_9, conjecture,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.21/0.60         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.21/0.60         ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.21/0.60       ( ![B:$i]:
% 0.21/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.60             ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.21/0.60             ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.60           ( ![C:$i]:
% 0.21/0.60             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.60               ( ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) =>
% 0.21/0.60                 ( r2_hidden @
% 0.21/0.60                   ( k12_lattice3 @ A @ C @ ( k11_yellow_6 @ A @ B ) ) @ 
% 0.21/0.60                   ( k10_yellow_6 @ A @ ( k3_waybel_2 @ A @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.60    (~( ![A:$i]:
% 0.21/0.60        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.21/0.60            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.21/0.60            ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.21/0.60          ( ![B:$i]:
% 0.21/0.60            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.60                ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.21/0.60                ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.60              ( ![C:$i]:
% 0.21/0.60                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.60                  ( ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) =>
% 0.21/0.60                    ( r2_hidden @
% 0.21/0.60                      ( k12_lattice3 @ A @ C @ ( k11_yellow_6 @ A @ B ) ) @ 
% 0.21/0.60                      ( k10_yellow_6 @ A @ ( k3_waybel_2 @ A @ C @ B ) ) ) ) ) ) ) ) ) )),
% 0.21/0.60    inference('cnf.neg', [status(esa)], [t26_waybel_9])).
% 0.21/0.60  thf('1', plain, ((v3_yellow_6 @ sk_B @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(dt_k11_yellow_6, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.60         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.21/0.60         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.60         ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.21/0.60         ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.60       ( m1_subset_1 @ ( k11_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.60  thf('2', plain,
% 0.21/0.60      (![X10 : $i, X11 : $i]:
% 0.21/0.60         (~ (l1_pre_topc @ X10)
% 0.21/0.60          | ~ (v8_pre_topc @ X10)
% 0.21/0.60          | ~ (v2_pre_topc @ X10)
% 0.21/0.60          | (v2_struct_0 @ X10)
% 0.21/0.60          | (v2_struct_0 @ X11)
% 0.21/0.60          | ~ (v4_orders_2 @ X11)
% 0.21/0.60          | ~ (v7_waybel_0 @ X11)
% 0.21/0.60          | ~ (v3_yellow_6 @ X11 @ X10)
% 0.21/0.60          | ~ (l1_waybel_0 @ X11 @ X10)
% 0.21/0.60          | (m1_subset_1 @ (k11_yellow_6 @ X10 @ X11) @ (u1_struct_0 @ X10)))),
% 0.21/0.60      inference('cnf', [status(esa)], [dt_k11_yellow_6])).
% 0.21/0.60  thf('3', plain,
% 0.21/0.60      (((m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.60        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.21/0.60        | ~ (v7_waybel_0 @ sk_B)
% 0.21/0.60        | ~ (v4_orders_2 @ sk_B)
% 0.21/0.60        | (v2_struct_0 @ sk_B)
% 0.21/0.60        | (v2_struct_0 @ sk_A)
% 0.21/0.60        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.60        | ~ (v8_pre_topc @ sk_A)
% 0.21/0.60        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.60  thf('4', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('5', plain, ((v7_waybel_0 @ sk_B)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('6', plain, ((v4_orders_2 @ sk_B)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('8', plain, ((v8_pre_topc @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('9', plain, ((l1_waybel_9 @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('10', plain,
% 0.21/0.60      (![X22 : $i]: ((l1_pre_topc @ X22) | ~ (l1_waybel_9 @ X22))),
% 0.21/0.60      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.21/0.60  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.60  thf('12', plain,
% 0.21/0.60      (((m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.60        | (v2_struct_0 @ sk_B)
% 0.21/0.60        | (v2_struct_0 @ sk_A))),
% 0.21/0.60      inference('demod', [status(thm)], ['3', '4', '5', '6', '7', '8', '11'])).
% 0.21/0.60  thf('13', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('14', plain,
% 0.21/0.60      (((v2_struct_0 @ sk_A)
% 0.21/0.60        | (m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.60      inference('clc', [status(thm)], ['12', '13'])).
% 0.21/0.60  thf('15', plain,
% 0.21/0.60      (![X22 : $i]: ((l1_orders_2 @ X22) | ~ (l1_waybel_9 @ X22))),
% 0.21/0.60      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.21/0.60  thf('16', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(redefinition_k12_lattice3, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.21/0.60         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.60         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.60       ( ( k12_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ B @ C ) ) ))).
% 0.21/0.60  thf('17', plain,
% 0.21/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.60         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.21/0.60          | ~ (l1_orders_2 @ X8)
% 0.21/0.60          | ~ (v2_lattice3 @ X8)
% 0.21/0.60          | ~ (v5_orders_2 @ X8)
% 0.21/0.60          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.60          | ((k12_lattice3 @ X8 @ X7 @ X9) = (k11_lattice3 @ X8 @ X7 @ X9)))),
% 0.21/0.60      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 0.21/0.60  thf('18', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         (((k12_lattice3 @ sk_A @ sk_C @ X0)
% 0.21/0.60            = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.21/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.60          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.60          | ~ (v2_lattice3 @ sk_A)
% 0.21/0.60          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.60  thf('19', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('20', plain, ((v2_lattice3 @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('21', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         (((k12_lattice3 @ sk_A @ sk_C @ X0)
% 0.21/0.60            = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.21/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.60          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.60      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.21/0.60  thf('22', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         (~ (l1_waybel_9 @ sk_A)
% 0.21/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.60          | ((k12_lattice3 @ sk_A @ sk_C @ X0)
% 0.21/0.60              = (k11_lattice3 @ sk_A @ sk_C @ X0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['15', '21'])).
% 0.21/0.60  thf('23', plain, ((l1_waybel_9 @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('24', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.60          | ((k12_lattice3 @ sk_A @ sk_C @ X0)
% 0.21/0.60              = (k11_lattice3 @ sk_A @ sk_C @ X0)))),
% 0.21/0.60      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.60  thf('25', plain,
% 0.21/0.60      (((v2_struct_0 @ sk_A)
% 0.21/0.60        | ((k12_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.21/0.60            = (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['14', '24'])).
% 0.21/0.60  thf('26', plain,
% 0.21/0.60      (((v2_struct_0 @ sk_A)
% 0.21/0.60        | (m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.60      inference('clc', [status(thm)], ['12', '13'])).
% 0.21/0.60  thf('27', plain,
% 0.21/0.60      (![X22 : $i]: ((l1_orders_2 @ X22) | ~ (l1_waybel_9 @ X22))),
% 0.21/0.60      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.21/0.60  thf('28', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(dt_k4_waybel_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.21/0.60         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.60       ( ( v1_funct_1 @ ( k4_waybel_1 @ A @ B ) ) & 
% 0.21/0.60         ( v1_funct_2 @
% 0.21/0.60           ( k4_waybel_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.60         ( m1_subset_1 @
% 0.21/0.60           ( k4_waybel_1 @ A @ B ) @ 
% 0.21/0.60           ( k1_zfmisc_1 @
% 0.21/0.60             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.60  thf('29', plain,
% 0.21/0.60      (![X20 : $i, X21 : $i]:
% 0.21/0.60         (~ (l1_orders_2 @ X20)
% 0.21/0.60          | (v2_struct_0 @ X20)
% 0.21/0.60          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.21/0.60          | (v1_funct_1 @ (k4_waybel_1 @ X20 @ X21)))),
% 0.21/0.60      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.21/0.60  thf('30', plain,
% 0.21/0.60      (((v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.21/0.60        | (v2_struct_0 @ sk_A)
% 0.21/0.60        | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.60  thf('31', plain,
% 0.21/0.60      ((~ (l1_waybel_9 @ sk_A)
% 0.21/0.60        | (v2_struct_0 @ sk_A)
% 0.21/0.60        | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['27', '30'])).
% 0.21/0.60  thf('32', plain, ((l1_waybel_9 @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('33', plain,
% 0.21/0.60      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.21/0.60      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.60  thf('34', plain,
% 0.21/0.60      (![X22 : $i]: ((l1_orders_2 @ X22) | ~ (l1_waybel_9 @ X22))),
% 0.21/0.60      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.21/0.60  thf('35', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('36', plain,
% 0.21/0.60      (![X20 : $i, X21 : $i]:
% 0.21/0.60         (~ (l1_orders_2 @ X20)
% 0.21/0.60          | (v2_struct_0 @ X20)
% 0.21/0.60          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.21/0.60          | (v1_funct_2 @ (k4_waybel_1 @ X20 @ X21) @ (u1_struct_0 @ X20) @ 
% 0.21/0.60             (u1_struct_0 @ X20)))),
% 0.21/0.60      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.21/0.60  thf('37', plain,
% 0.21/0.60      (((v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.60         (u1_struct_0 @ sk_A))
% 0.21/0.60        | (v2_struct_0 @ sk_A)
% 0.21/0.60        | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.60      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.60  thf('38', plain,
% 0.21/0.60      ((~ (l1_waybel_9 @ sk_A)
% 0.21/0.60        | (v2_struct_0 @ sk_A)
% 0.21/0.60        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.60           (u1_struct_0 @ sk_A)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['34', '37'])).
% 0.21/0.60  thf('39', plain, ((l1_waybel_9 @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('40', plain,
% 0.21/0.60      (((v2_struct_0 @ sk_A)
% 0.21/0.60        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.60           (u1_struct_0 @ sk_A)))),
% 0.21/0.60      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.60  thf('41', plain,
% 0.21/0.60      (![X22 : $i]: ((l1_orders_2 @ X22) | ~ (l1_waybel_9 @ X22))),
% 0.21/0.60      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.21/0.60  thf('42', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('43', plain,
% 0.21/0.60      (![X20 : $i, X21 : $i]:
% 0.21/0.60         (~ (l1_orders_2 @ X20)
% 0.21/0.60          | (v2_struct_0 @ X20)
% 0.21/0.60          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.21/0.60          | (m1_subset_1 @ (k4_waybel_1 @ X20 @ X21) @ 
% 0.21/0.60             (k1_zfmisc_1 @ 
% 0.21/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X20)))))),
% 0.21/0.60      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.21/0.60  thf('44', plain,
% 0.21/0.60      (((m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.21/0.60         (k1_zfmisc_1 @ 
% 0.21/0.60          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.21/0.60        | (v2_struct_0 @ sk_A)
% 0.21/0.60        | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.61      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.61  thf('45', plain,
% 0.21/0.61      ((~ (l1_waybel_9 @ sk_A)
% 0.21/0.61        | (v2_struct_0 @ sk_A)
% 0.21/0.61        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.21/0.61           (k1_zfmisc_1 @ 
% 0.21/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.61      inference('sup-', [status(thm)], ['41', '44'])).
% 0.21/0.61  thf('46', plain, ((l1_waybel_9 @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('47', plain,
% 0.21/0.61      (((v2_struct_0 @ sk_A)
% 0.21/0.61        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.21/0.61           (k1_zfmisc_1 @ 
% 0.21/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.61      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.61  thf(redefinition_k3_funct_2, axiom,
% 0.21/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.61         ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.61         ( m1_subset_1 @ D @ A ) ) =>
% 0.21/0.61       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.21/0.61  thf('48', plain,
% 0.21/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.21/0.61          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.21/0.61          | ~ (v1_funct_1 @ X0)
% 0.21/0.61          | (v1_xboole_0 @ X1)
% 0.21/0.61          | ~ (m1_subset_1 @ X3 @ X1)
% 0.21/0.61          | ((k3_funct_2 @ X1 @ X2 @ X0 @ X3) = (k1_funct_1 @ X0 @ X3)))),
% 0.21/0.61      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.61  thf('49', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((v2_struct_0 @ sk_A)
% 0.21/0.61          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.21/0.61              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.21/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.21/0.61          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.21/0.61               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.61  thf('50', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((v2_struct_0 @ sk_A)
% 0.21/0.61          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.21/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.21/0.61              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.21/0.61          | (v2_struct_0 @ sk_A))),
% 0.21/0.61      inference('sup-', [status(thm)], ['40', '49'])).
% 0.21/0.61  thf('51', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61            (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.21/0.61            = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.21/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.21/0.61          | (v2_struct_0 @ sk_A))),
% 0.21/0.61      inference('simplify', [status(thm)], ['50'])).
% 0.21/0.61  thf('52', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((v2_struct_0 @ sk_A)
% 0.21/0.61          | (v2_struct_0 @ sk_A)
% 0.21/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.21/0.61              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['33', '51'])).
% 0.21/0.61  thf('53', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61            (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.21/0.61            = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.21/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | (v2_struct_0 @ sk_A))),
% 0.21/0.61      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.61  thf('54', plain,
% 0.21/0.61      (((v2_struct_0 @ sk_A)
% 0.21/0.61        | (v2_struct_0 @ sk_A)
% 0.21/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61        | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.21/0.61            = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.21/0.61               (k11_yellow_6 @ sk_A @ sk_B))))),
% 0.21/0.61      inference('sup-', [status(thm)], ['26', '53'])).
% 0.21/0.61  thf('55', plain,
% 0.21/0.61      ((((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.21/0.61          = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.21/0.61             (k11_yellow_6 @ sk_A @ sk_B)))
% 0.21/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61        | (v2_struct_0 @ sk_A))),
% 0.21/0.61      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.61  thf('56', plain,
% 0.21/0.61      (((v2_struct_0 @ sk_A)
% 0.21/0.61        | (m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('clc', [status(thm)], ['12', '13'])).
% 0.21/0.61  thf('57', plain,
% 0.21/0.61      (![X22 : $i]: ((l1_orders_2 @ X22) | ~ (l1_waybel_9 @ X22))),
% 0.21/0.61      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.21/0.61  thf('58', plain,
% 0.21/0.61      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.21/0.61      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.61  thf('59', plain,
% 0.21/0.61      (((v2_struct_0 @ sk_A)
% 0.21/0.61        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61           (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.61  thf('60', plain,
% 0.21/0.61      (((v2_struct_0 @ sk_A)
% 0.21/0.61        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.21/0.61           (k1_zfmisc_1 @ 
% 0.21/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.61      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.61  thf(d18_waybel_1, axiom,
% 0.21/0.61    (![A:$i]:
% 0.21/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.61       ( ![B:$i]:
% 0.21/0.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.61           ( ![C:$i]:
% 0.21/0.61             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.61                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.61                 ( m1_subset_1 @
% 0.21/0.61                   C @ 
% 0.21/0.61                   ( k1_zfmisc_1 @
% 0.21/0.61                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.61               ( ( ( C ) = ( k4_waybel_1 @ A @ B ) ) <=>
% 0.21/0.61                 ( ![D:$i]:
% 0.21/0.61                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.61                     ( ( k3_funct_2 @
% 0.21/0.61                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ C @ D ) =
% 0.21/0.61                       ( k11_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.61  thf('61', plain,
% 0.21/0.61      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.61         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.21/0.61          | ((X18) != (k4_waybel_1 @ X17 @ X16))
% 0.21/0.61          | ((k3_funct_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X17) @ X18 @ 
% 0.21/0.61              X19) = (k11_lattice3 @ X17 @ X16 @ X19))
% 0.21/0.61          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.21/0.61          | ~ (m1_subset_1 @ X18 @ 
% 0.21/0.61               (k1_zfmisc_1 @ 
% 0.21/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X17))))
% 0.21/0.61          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X17))
% 0.21/0.61          | ~ (v1_funct_1 @ X18)
% 0.21/0.61          | ~ (l1_orders_2 @ X17)
% 0.21/0.61          | (v2_struct_0 @ X17))),
% 0.21/0.61      inference('cnf', [status(esa)], [d18_waybel_1])).
% 0.21/0.61  thf('62', plain,
% 0.21/0.61      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.21/0.61         ((v2_struct_0 @ X17)
% 0.21/0.61          | ~ (l1_orders_2 @ X17)
% 0.21/0.61          | ~ (v1_funct_1 @ (k4_waybel_1 @ X17 @ X16))
% 0.21/0.61          | ~ (v1_funct_2 @ (k4_waybel_1 @ X17 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.21/0.61               (u1_struct_0 @ X17))
% 0.21/0.61          | ~ (m1_subset_1 @ (k4_waybel_1 @ X17 @ X16) @ 
% 0.21/0.61               (k1_zfmisc_1 @ 
% 0.21/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X17))))
% 0.21/0.61          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.21/0.61          | ((k3_funct_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X17) @ 
% 0.21/0.61              (k4_waybel_1 @ X17 @ X16) @ X19)
% 0.21/0.61              = (k11_lattice3 @ X17 @ X16 @ X19))
% 0.21/0.61          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17)))),
% 0.21/0.61      inference('simplify', [status(thm)], ['61'])).
% 0.21/0.61  thf('63', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((v2_struct_0 @ sk_A)
% 0.21/0.61          | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.21/0.61              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.21/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.21/0.61               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.21/0.61          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.61          | (v2_struct_0 @ sk_A))),
% 0.21/0.61      inference('sup-', [status(thm)], ['60', '62'])).
% 0.21/0.61  thf('64', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('65', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((v2_struct_0 @ sk_A)
% 0.21/0.61          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.21/0.61              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.21/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.21/0.61               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.21/0.61          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.61          | (v2_struct_0 @ sk_A))),
% 0.21/0.61      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.61  thf('66', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (l1_orders_2 @ sk_A)
% 0.21/0.61          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.21/0.61          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.21/0.61               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.21/0.61              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.21/0.61          | (v2_struct_0 @ sk_A))),
% 0.21/0.61      inference('simplify', [status(thm)], ['65'])).
% 0.21/0.61  thf('67', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((v2_struct_0 @ sk_A)
% 0.21/0.61          | (v2_struct_0 @ sk_A)
% 0.21/0.61          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.21/0.61              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.21/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.21/0.61          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.61      inference('sup-', [status(thm)], ['59', '66'])).
% 0.21/0.61  thf('68', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (l1_orders_2 @ sk_A)
% 0.21/0.61          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.21/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.21/0.61              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.21/0.61          | (v2_struct_0 @ sk_A))),
% 0.21/0.61      inference('simplify', [status(thm)], ['67'])).
% 0.21/0.61  thf('69', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((v2_struct_0 @ sk_A)
% 0.21/0.61          | (v2_struct_0 @ sk_A)
% 0.21/0.61          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.21/0.61              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.21/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.61      inference('sup-', [status(thm)], ['58', '68'])).
% 0.21/0.61  thf('70', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (l1_orders_2 @ sk_A)
% 0.21/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.21/0.61              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.21/0.61          | (v2_struct_0 @ sk_A))),
% 0.21/0.61      inference('simplify', [status(thm)], ['69'])).
% 0.21/0.61  thf('71', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         (~ (l1_waybel_9 @ sk_A)
% 0.21/0.61          | (v2_struct_0 @ sk_A)
% 0.21/0.61          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.21/0.61              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.21/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('sup-', [status(thm)], ['57', '70'])).
% 0.21/0.61  thf('72', plain, ((l1_waybel_9 @ sk_A)),
% 0.21/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.61  thf('73', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((v2_struct_0 @ sk_A)
% 0.21/0.61          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.21/0.61              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.21/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('demod', [status(thm)], ['71', '72'])).
% 0.21/0.61  thf('74', plain,
% 0.21/0.61      (((v2_struct_0 @ sk_A)
% 0.21/0.61        | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.21/0.61            = (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)))
% 0.21/0.61        | (v2_struct_0 @ sk_A))),
% 0.21/0.61      inference('sup-', [status(thm)], ['56', '73'])).
% 0.21/0.61  thf('75', plain,
% 0.21/0.61      ((((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.21/0.61          = (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)))
% 0.21/0.61        | (v2_struct_0 @ sk_A))),
% 0.21/0.61      inference('simplify', [status(thm)], ['74'])).
% 0.21/0.61  thf('76', plain,
% 0.21/0.61      ((((k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.21/0.61          (k11_yellow_6 @ sk_A @ sk_B))
% 0.21/0.61          = (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)))
% 0.21/0.61        | (v2_struct_0 @ sk_A)
% 0.21/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61        | (v2_struct_0 @ sk_A))),
% 0.21/0.61      inference('sup+', [status(thm)], ['55', '75'])).
% 0.21/0.61  thf('77', plain,
% 0.21/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.61        | (v2_struct_0 @ sk_A)
% 0.21/0.61        | ((k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.21/0.61            (k11_yellow_6 @ sk_A @ sk_B))
% 0.21/0.61            = (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B))))),
% 0.21/0.61      inference('simplify', [status(thm)], ['76'])).
% 0.21/0.61  thf('78', plain,
% 0.21/0.61      (((v2_struct_0 @ sk_A)
% 0.21/0.61        | (m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('clc', [status(thm)], ['12', '13'])).
% 0.21/0.61  thf('79', plain,
% 0.21/0.61      (![X22 : $i]: ((l1_orders_2 @ X22) | ~ (l1_waybel_9 @ X22))),
% 0.21/0.61      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.21/0.61  thf('80', plain,
% 0.21/0.61      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.21/0.61      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.61  thf('81', plain,
% 0.21/0.61      (((v2_struct_0 @ sk_A)
% 0.21/0.61        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.61           (u1_struct_0 @ sk_A)))),
% 0.21/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.61  thf('82', plain,
% 0.21/0.61      (((v2_struct_0 @ sk_A)
% 0.21/0.61        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.21/0.61           (k1_zfmisc_1 @ 
% 0.21/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.61      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.61  thf(redefinition_k2_yellow_6, axiom,
% 0.21/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.21/0.61         ( l1_orders_2 @ B ) & ( v1_funct_1 @ C ) & 
% 0.21/0.61         ( v1_funct_2 @ C @ A @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.61         ( m1_subset_1 @
% 0.21/0.61           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.21/0.61         ( m1_subset_1 @ D @ A ) ) =>
% 0.21/0.61       ( ( k2_yellow_6 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.21/0.61  thf('83', plain,
% 0.21/0.61      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.61         (~ (m1_subset_1 @ X12 @ 
% 0.21/0.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ (u1_struct_0 @ X14))))
% 0.21/0.61          | ~ (v1_funct_2 @ X12 @ X13 @ (u1_struct_0 @ X14))
% 0.21/0.61          | ~ (v1_funct_1 @ X12)
% 0.21/0.61          | ~ (l1_orders_2 @ X14)
% 0.21/0.61          | (v2_struct_0 @ X14)
% 0.21/0.61          | (v1_xboole_0 @ X13)
% 0.21/0.61          | ~ (m1_subset_1 @ X15 @ X13)
% 0.21/0.61          | ((k2_yellow_6 @ X13 @ X14 @ X12 @ X15) = (k1_funct_1 @ X12 @ X15)))),
% 0.21/0.61      inference('cnf', [status(esa)], [redefinition_k2_yellow_6])).
% 0.21/0.61  thf('84', plain,
% 0.21/0.61      (![X0 : $i]:
% 0.21/0.61         ((v2_struct_0 @ sk_A)
% 0.21/0.61          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.43/0.61              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.43/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | (v2_struct_0 @ sk_A)
% 0.43/0.61          | ~ (l1_orders_2 @ sk_A)
% 0.43/0.61          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.43/0.61          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.43/0.61               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['82', '83'])).
% 0.43/0.61  thf('85', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.61             (u1_struct_0 @ sk_A))
% 0.43/0.61          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.43/0.61          | ~ (l1_orders_2 @ sk_A)
% 0.43/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.43/0.61              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.43/0.61          | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('simplify', [status(thm)], ['84'])).
% 0.43/0.61  thf('86', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_A)
% 0.43/0.61          | (v2_struct_0 @ sk_A)
% 0.43/0.61          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.43/0.61              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.43/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | ~ (l1_orders_2 @ sk_A)
% 0.43/0.61          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['81', '85'])).
% 0.43/0.61  thf('87', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.43/0.61          | ~ (l1_orders_2 @ sk_A)
% 0.43/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.43/0.61              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.43/0.61          | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('simplify', [status(thm)], ['86'])).
% 0.43/0.61  thf('88', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_A)
% 0.43/0.61          | (v2_struct_0 @ sk_A)
% 0.43/0.61          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.43/0.61              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.43/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | ~ (l1_orders_2 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['80', '87'])).
% 0.43/0.61  thf('89', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (l1_orders_2 @ sk_A)
% 0.43/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.43/0.61              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.43/0.61          | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('simplify', [status(thm)], ['88'])).
% 0.43/0.61  thf('90', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (l1_waybel_9 @ sk_A)
% 0.43/0.61          | (v2_struct_0 @ sk_A)
% 0.43/0.61          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.43/0.61              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.43/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['79', '89'])).
% 0.43/0.61  thf('91', plain, ((l1_waybel_9 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('92', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_A)
% 0.43/0.61          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.43/0.61              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.43/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['90', '91'])).
% 0.43/0.61  thf('93', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.43/0.61            = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.43/0.61               (k11_yellow_6 @ sk_A @ sk_B)))
% 0.43/0.61        | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['78', '92'])).
% 0.43/0.61  thf('94', plain,
% 0.43/0.61      ((((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.43/0.61          = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.43/0.61             (k11_yellow_6 @ sk_A @ sk_B)))
% 0.43/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('simplify', [status(thm)], ['93'])).
% 0.43/0.61  thf('95', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('96', plain,
% 0.43/0.61      (![X22 : $i]: ((l1_orders_2 @ X22) | ~ (l1_waybel_9 @ X22))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.43/0.61  thf('97', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t18_waybel_9, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.43/0.61           ( ![C:$i]:
% 0.43/0.61             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61               ( ( k6_waybel_9 @ A @ A @ ( k4_waybel_1 @ A @ C ) @ B ) =
% 0.43/0.61                 ( k3_waybel_2 @ A @ C @ B ) ) ) ) ) ) ))).
% 0.43/0.61  thf('98', plain,
% 0.43/0.61      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X23)
% 0.43/0.61          | ~ (l1_waybel_0 @ X23 @ X24)
% 0.43/0.61          | ((k6_waybel_9 @ X24 @ X24 @ (k4_waybel_1 @ X24 @ X25) @ X23)
% 0.43/0.61              = (k3_waybel_2 @ X24 @ X25 @ X23))
% 0.43/0.61          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.43/0.61          | ~ (l1_orders_2 @ X24)
% 0.43/0.61          | (v2_struct_0 @ X24))),
% 0.43/0.61      inference('cnf', [status(esa)], [t18_waybel_9])).
% 0.43/0.61  thf('99', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_A)
% 0.43/0.61          | ~ (l1_orders_2 @ sk_A)
% 0.43/0.61          | ((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.43/0.61              = (k3_waybel_2 @ sk_A @ sk_C @ X0))
% 0.43/0.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.43/0.61          | (v2_struct_0 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['97', '98'])).
% 0.43/0.61  thf('100', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (l1_waybel_9 @ sk_A)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.43/0.61          | ((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.43/0.61              = (k3_waybel_2 @ sk_A @ sk_C @ X0))
% 0.43/0.61          | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['96', '99'])).
% 0.43/0.61  thf('101', plain, ((l1_waybel_9 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('102', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X0)
% 0.43/0.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.43/0.61          | ((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.43/0.61              = (k3_waybel_2 @ sk_A @ sk_C @ X0))
% 0.43/0.61          | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['100', '101'])).
% 0.43/0.61  thf('103', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B)
% 0.43/0.61            = (k3_waybel_2 @ sk_A @ sk_C @ sk_B))
% 0.43/0.61        | (v2_struct_0 @ sk_B))),
% 0.43/0.61      inference('sup-', [status(thm)], ['95', '102'])).
% 0.43/0.61  thf('104', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('105', plain,
% 0.43/0.61      ((((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B)
% 0.43/0.61          = (k3_waybel_2 @ sk_A @ sk_C @ sk_B))
% 0.43/0.61        | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('clc', [status(thm)], ['103', '104'])).
% 0.43/0.61  thf('106', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('107', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.43/0.61      inference('demod', [status(thm)], ['31', '32'])).
% 0.43/0.61  thf('108', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.61           (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.43/0.61  thf('109', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.43/0.61           (k1_zfmisc_1 @ 
% 0.43/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.43/0.61      inference('demod', [status(thm)], ['45', '46'])).
% 0.43/0.61  thf(t25_waybel_9, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.43/0.61         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.43/0.61         ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.43/0.61             ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.43/0.61             ( l1_waybel_0 @ B @ A ) ) =>
% 0.43/0.61           ( ![C:$i]:
% 0.43/0.61             ( ( ( v1_funct_1 @ C ) & 
% 0.43/0.61                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.43/0.61                 ( m1_subset_1 @
% 0.43/0.61                   C @ 
% 0.43/0.61                   ( k1_zfmisc_1 @
% 0.43/0.61                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.43/0.61               ( ( v5_pre_topc @ C @ A @ A ) =>
% 0.43/0.61                 ( r2_hidden @
% 0.43/0.61                   ( k2_yellow_6 @
% 0.43/0.61                     ( u1_struct_0 @ A ) @ A @ C @ ( k11_yellow_6 @ A @ B ) ) @ 
% 0.43/0.61                   ( k10_yellow_6 @ A @ ( k6_waybel_9 @ A @ A @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.43/0.61  thf('110', plain,
% 0.43/0.61      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X26)
% 0.43/0.61          | ~ (v4_orders_2 @ X26)
% 0.43/0.61          | ~ (v7_waybel_0 @ X26)
% 0.43/0.61          | ~ (v3_yellow_6 @ X26 @ X27)
% 0.43/0.61          | ~ (l1_waybel_0 @ X26 @ X27)
% 0.43/0.61          | ~ (v5_pre_topc @ X28 @ X27 @ X27)
% 0.43/0.61          | (r2_hidden @ 
% 0.43/0.61             (k2_yellow_6 @ (u1_struct_0 @ X27) @ X27 @ X28 @ 
% 0.43/0.61              (k11_yellow_6 @ X27 @ X26)) @ 
% 0.43/0.61             (k10_yellow_6 @ X27 @ (k6_waybel_9 @ X27 @ X27 @ X28 @ X26)))
% 0.43/0.61          | ~ (m1_subset_1 @ X28 @ 
% 0.43/0.61               (k1_zfmisc_1 @ 
% 0.43/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X27))))
% 0.43/0.61          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X27))
% 0.43/0.61          | ~ (v1_funct_1 @ X28)
% 0.43/0.61          | ~ (l1_waybel_9 @ X27)
% 0.43/0.61          | ~ (v2_lattice3 @ X27)
% 0.43/0.61          | ~ (v1_lattice3 @ X27)
% 0.43/0.61          | ~ (v5_orders_2 @ X27)
% 0.43/0.61          | ~ (v4_orders_2 @ X27)
% 0.43/0.61          | ~ (v3_orders_2 @ X27)
% 0.43/0.61          | ~ (v8_pre_topc @ X27)
% 0.43/0.61          | ~ (v2_pre_topc @ X27))),
% 0.43/0.61      inference('cnf', [status(esa)], [t25_waybel_9])).
% 0.43/0.61  thf('111', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_A)
% 0.43/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61          | ~ (v8_pre_topc @ sk_A)
% 0.43/0.61          | ~ (v3_orders_2 @ sk_A)
% 0.43/0.61          | ~ (v4_orders_2 @ sk_A)
% 0.43/0.61          | ~ (v5_orders_2 @ sk_A)
% 0.43/0.61          | ~ (v1_lattice3 @ sk_A)
% 0.43/0.61          | ~ (v2_lattice3 @ sk_A)
% 0.43/0.61          | ~ (l1_waybel_9 @ sk_A)
% 0.43/0.61          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.43/0.61          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.43/0.61               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | (r2_hidden @ 
% 0.43/0.61             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.43/0.61             (k10_yellow_6 @ sk_A @ 
% 0.43/0.61              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.43/0.61          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_A @ sk_A)
% 0.43/0.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.43/0.61          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.43/0.61          | ~ (v7_waybel_0 @ X0)
% 0.43/0.61          | ~ (v4_orders_2 @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['109', '110'])).
% 0.43/0.61  thf('112', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('113', plain, ((v8_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('114', plain, ((v3_orders_2 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('115', plain, ((v4_orders_2 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('116', plain, ((v5_orders_2 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('117', plain, ((v1_lattice3 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('118', plain, ((v2_lattice3 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('119', plain, ((l1_waybel_9 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('120', plain,
% 0.43/0.61      ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_A @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('121', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_A)
% 0.43/0.61          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.43/0.61          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.43/0.61               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | (r2_hidden @ 
% 0.43/0.61             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.43/0.61             (k10_yellow_6 @ sk_A @ 
% 0.43/0.61              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.43/0.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.43/0.61          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.43/0.61          | ~ (v7_waybel_0 @ X0)
% 0.43/0.61          | ~ (v4_orders_2 @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0))),
% 0.43/0.61      inference('demod', [status(thm)],
% 0.43/0.61                ['111', '112', '113', '114', '115', '116', '117', '118', 
% 0.43/0.61                 '119', '120'])).
% 0.43/0.61  thf('122', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_A)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v4_orders_2 @ X0)
% 0.43/0.61          | ~ (v7_waybel_0 @ X0)
% 0.43/0.61          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.43/0.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.43/0.61          | (r2_hidden @ 
% 0.43/0.61             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.43/0.61             (k10_yellow_6 @ sk_A @ 
% 0.43/0.61              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.43/0.61          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.43/0.61          | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['108', '121'])).
% 0.43/0.61  thf('123', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.43/0.61          | (r2_hidden @ 
% 0.43/0.61             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.43/0.61             (k10_yellow_6 @ sk_A @ 
% 0.43/0.61              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.43/0.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.43/0.61          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.43/0.61          | ~ (v7_waybel_0 @ X0)
% 0.43/0.61          | ~ (v4_orders_2 @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('simplify', [status(thm)], ['122'])).
% 0.43/0.61  thf('124', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_A)
% 0.43/0.61          | (v2_struct_0 @ sk_A)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v4_orders_2 @ X0)
% 0.43/0.61          | ~ (v7_waybel_0 @ X0)
% 0.43/0.61          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.43/0.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.43/0.61          | (r2_hidden @ 
% 0.43/0.61             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.43/0.61             (k10_yellow_6 @ sk_A @ 
% 0.43/0.61              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['107', '123'])).
% 0.43/0.61  thf('125', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((r2_hidden @ 
% 0.43/0.61           (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.43/0.61           (k10_yellow_6 @ sk_A @ 
% 0.43/0.61            (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.43/0.61          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.43/0.61          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.43/0.61          | ~ (v7_waybel_0 @ X0)
% 0.43/0.61          | ~ (v4_orders_2 @ X0)
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('simplify', [status(thm)], ['124'])).
% 0.43/0.61  thf('126', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | (v2_struct_0 @ sk_B)
% 0.43/0.61        | ~ (v4_orders_2 @ sk_B)
% 0.43/0.61        | ~ (v7_waybel_0 @ sk_B)
% 0.43/0.61        | ~ (v3_yellow_6 @ sk_B @ sk_A)
% 0.43/0.61        | (r2_hidden @ 
% 0.43/0.61           (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.43/0.61           (k10_yellow_6 @ sk_A @ 
% 0.43/0.61            (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['106', '125'])).
% 0.43/0.61  thf('127', plain, ((v4_orders_2 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('128', plain, ((v7_waybel_0 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('129', plain, ((v3_yellow_6 @ sk_B @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('130', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | (v2_struct_0 @ sk_B)
% 0.43/0.61        | (r2_hidden @ 
% 0.43/0.61           (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.43/0.61           (k10_yellow_6 @ sk_A @ 
% 0.43/0.61            (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B))))),
% 0.43/0.61      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 0.43/0.61  thf('131', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('132', plain,
% 0.43/0.61      (((r2_hidden @ 
% 0.43/0.61         (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.43/0.61         (k10_yellow_6 @ sk_A @ 
% 0.43/0.61          (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B)))
% 0.43/0.61        | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('clc', [status(thm)], ['130', '131'])).
% 0.43/0.61  thf('133', plain,
% 0.43/0.61      (((r2_hidden @ 
% 0.43/0.61         (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.43/0.61         (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('sup+', [status(thm)], ['105', '132'])).
% 0.43/0.61  thf('134', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | (r2_hidden @ 
% 0.43/0.61           (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.43/0.61            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.43/0.61           (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B))))),
% 0.43/0.61      inference('simplify', [status(thm)], ['133'])).
% 0.43/0.61  thf('135', plain,
% 0.43/0.61      (((r2_hidden @ 
% 0.43/0.61         (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.43/0.61          (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.43/0.61         (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('sup+', [status(thm)], ['94', '134'])).
% 0.43/0.61  thf('136', plain,
% 0.43/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | (r2_hidden @ 
% 0.43/0.61           (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.43/0.61            (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.43/0.61           (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B))))),
% 0.43/0.61      inference('simplify', [status(thm)], ['135'])).
% 0.43/0.61  thf('137', plain,
% 0.43/0.61      (((r2_hidden @ 
% 0.43/0.61         (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.43/0.61         (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['77', '136'])).
% 0.43/0.61  thf('138', plain,
% 0.43/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | (r2_hidden @ 
% 0.43/0.61           (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.43/0.61           (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B))))),
% 0.43/0.61      inference('simplify', [status(thm)], ['137'])).
% 0.43/0.61  thf('139', plain,
% 0.43/0.61      (((r2_hidden @ 
% 0.43/0.61         (k12_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.43/0.61         (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['25', '138'])).
% 0.43/0.61  thf('140', plain,
% 0.43/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | (r2_hidden @ 
% 0.43/0.61           (k12_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.43/0.61           (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B))))),
% 0.43/0.61      inference('simplify', [status(thm)], ['139'])).
% 0.43/0.61  thf('141', plain,
% 0.43/0.61      (~ (r2_hidden @ 
% 0.43/0.61          (k12_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.43/0.61          (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('142', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('clc', [status(thm)], ['140', '141'])).
% 0.43/0.61  thf(fc2_struct_0, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.43/0.61       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.43/0.61  thf('143', plain,
% 0.43/0.61      (![X5 : $i]:
% 0.43/0.61         (~ (v1_xboole_0 @ (u1_struct_0 @ X5))
% 0.43/0.61          | ~ (l1_struct_0 @ X5)
% 0.43/0.61          | (v2_struct_0 @ X5))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.43/0.61  thf('144', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['142', '143'])).
% 0.43/0.61  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.43/0.61  thf(dt_l1_pre_topc, axiom,
% 0.43/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.43/0.61  thf('146', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.43/0.61  thf('147', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.61      inference('sup-', [status(thm)], ['145', '146'])).
% 0.43/0.61  thf('148', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['144', '147'])).
% 0.43/0.61  thf('149', plain, ((v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('simplify', [status(thm)], ['148'])).
% 0.43/0.61  thf(cc2_lattice3, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( l1_orders_2 @ A ) =>
% 0.43/0.61       ( ( v2_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.43/0.61  thf('150', plain,
% 0.43/0.61      (![X6 : $i]:
% 0.43/0.61         (~ (v2_lattice3 @ X6) | ~ (v2_struct_0 @ X6) | ~ (l1_orders_2 @ X6))),
% 0.43/0.61      inference('cnf', [status(esa)], [cc2_lattice3])).
% 0.43/0.61  thf('151', plain, ((~ (l1_orders_2 @ sk_A) | ~ (v2_lattice3 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['149', '150'])).
% 0.43/0.61  thf('152', plain, ((v2_lattice3 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('153', plain, (~ (l1_orders_2 @ sk_A)),
% 0.43/0.61      inference('demod', [status(thm)], ['151', '152'])).
% 0.43/0.61  thf('154', plain, (~ (l1_waybel_9 @ sk_A)),
% 0.43/0.61      inference('sup-', [status(thm)], ['0', '153'])).
% 0.43/0.61  thf('155', plain, ((l1_waybel_9 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('156', plain, ($false), inference('demod', [status(thm)], ['154', '155'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
