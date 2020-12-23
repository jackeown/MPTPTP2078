%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qa71D2LyXb

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:30 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  223 ( 530 expanded)
%              Number of leaves         :   52 ( 177 expanded)
%              Depth                    :   36
%              Number of atoms          : 2719 (12832 expanded)
%              Number of equality atoms :   55 (  55 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k6_waybel_9_type,type,(
    k6_waybel_9: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k11_yellow_6_type,type,(
    k11_yellow_6: $i > $i > $i )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k3_waybel_2_type,type,(
    k3_waybel_2: $i > $i > $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_yellow_6_type,type,(
    k2_yellow_6: $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(dt_l1_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_waybel_9 @ A )
     => ( ( l1_pre_topc @ A )
        & ( l1_orders_2 @ A ) ) ) )).

thf('0',plain,(
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('1',plain,(
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('2',plain,(
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('4',plain,(
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

thf('5',plain,(
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

thf('6',plain,
    ( ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X23: $i] :
      ( ( l1_pre_topc @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7','8','9','10','11','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v2_lattice3 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( ( k12_lattice3 @ X8 @ X7 @ X9 )
        = ( k11_lattice3 @ X8 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k12_lattice3])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ sk_A @ sk_C @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k12_lattice3 @ sk_A @ sk_C @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k12_lattice3 @ sk_A @ sk_C @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k12_lattice3 @ sk_A @ sk_C @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k12_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','27'])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('30',plain,(
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('31',plain,(
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( v1_funct_1 @ ( k4_waybel_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('34',plain,
    ( ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( v1_funct_2 @ ( k4_waybel_1 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('41',plain,
    ( ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( m1_subset_1 @ ( k4_waybel_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X21 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_1])).

thf('48',plain,
    ( ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

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

thf('52',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( X19
       != ( k4_waybel_1 @ X18 @ X17 ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X18 ) @ X19 @ X20 )
        = ( k11_lattice3 @ X18 @ X17 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_waybel_1])).

thf('53',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ X18 @ X17 ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ X18 @ X17 ) @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ ( k4_waybel_1 @ X18 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X18 ) @ ( k4_waybel_1 @ X18 @ X17 ) @ X20 )
        = ( k11_lattice3 @ X18 @ X17 @ X20 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
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
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','61'])).

thf('63',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k11_lattice3 @ sk_A @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','64'])).

thf('66',plain,
    ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X3 @ X1 )
      | ( ( k3_funct_2 @ X1 @ X2 @ X0 @ X3 )
        = ( k1_funct_1 @ X0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['67','76'])).

thf('78',plain,
    ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['66','78'])).

thf('80',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k11_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('82',plain,(
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

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

thf('86',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( l1_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ X14 )
      | ( ( k2_yellow_6 @ X14 @ X15 @ X13 @ X16 )
        = ( k1_funct_1 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_yellow_6])).

thf('87',plain,(
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
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
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
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['84','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['82','92'])).

thf('94',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','95'])).

thf('97',plain,
    ( ( ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('100',plain,(
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

thf('101',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_waybel_0 @ X24 @ X25 )
      | ( ( k6_waybel_9 @ X25 @ X25 @ ( k4_waybel_1 @ X25 @ X26 ) @ X24 )
        = ( k3_waybel_2 @ X25 @ X26 @ X24 ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t18_waybel_9])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k3_waybel_2 @ sk_A @ sk_C @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k3_waybel_2 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 )
        = ( k3_waybel_2 @ sk_A @ sk_C @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ sk_B )
      = ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['98','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ sk_B )
      = ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

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

thf('113',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ~ ( v7_waybel_0 @ X27 )
      | ~ ( v3_yellow_6 @ X27 @ X28 )
      | ~ ( l1_waybel_0 @ X27 @ X28 )
      | ~ ( v5_pre_topc @ X29 @ X28 @ X28 )
      | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ X28 ) @ X28 @ X29 @ ( k11_yellow_6 @ X28 @ X27 ) ) @ ( k10_yellow_6 @ X28 @ ( k6_waybel_9 @ X28 @ X28 @ X29 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( l1_waybel_9 @ X28 )
      | ~ ( v2_lattice3 @ X28 )
      | ~ ( v1_lattice3 @ X28 )
      | ~ ( v5_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ~ ( v8_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t25_waybel_9])).

thf('114',plain,(
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
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v5_pre_topc @ ( k4_waybel_1 @ sk_A @ sk_C ) @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
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
    inference(demod,[status(thm)],['114','115','116','117','118','119','120','121','122','123'])).

thf('125',plain,(
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
    inference('sup-',[status(thm)],['111','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) )
      | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ X0 ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v3_yellow_6 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v3_yellow_6 @ X0 @ sk_A )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ X0 ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['110','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ X0 ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ X0 ) ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v3_yellow_6 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v3_yellow_6 @ sk_B @ sk_A )
    | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['109','128'])).

thf('130',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v3_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k6_waybel_9 @ sk_A @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['108','135'])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k2_yellow_6 @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['97','137'])).

thf('139',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_funct_1 @ ( k4_waybel_1 @ sk_A @ sk_C ) @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( ( r2_hidden @ ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['80','139'])).

thf('141',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k11_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ( r2_hidden @ ( k12_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','141'])).

thf('143',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k12_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ~ ( r2_hidden @ ( k12_lattice3 @ sk_A @ sk_C @ ( k11_yellow_6 @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( k3_waybel_2 @ sk_A @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['3','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('148',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('149',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['146','149'])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('151',plain,(
    ! [X6: $i] :
      ( ~ ( v1_lattice3 @ X6 )
      | ~ ( v2_struct_0 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('152',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','154'])).

thf('156',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['155','156'])).

thf(fc2_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('158',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_yellow_0])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','159'])).

thf('161',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X6: $i] :
      ( ~ ( v1_lattice3 @ X6 )
      | ~ ( v2_struct_0 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('164',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','166'])).

thf('168',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    $false ),
    inference(demod,[status(thm)],['167','168'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qa71D2LyXb
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.74  % Solved by: fo/fo7.sh
% 0.54/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.74  % done 463 iterations in 0.284s
% 0.54/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.74  % SZS output start Refutation
% 0.54/0.74  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.54/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.74  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.54/0.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.54/0.74  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.54/0.74  thf(k12_lattice3_type, type, k12_lattice3: $i > $i > $i > $i).
% 0.54/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.74  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.54/0.74  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.54/0.74  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.54/0.74  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.54/0.74  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.54/0.74  thf(v3_yellow_6_type, type, v3_yellow_6: $i > $i > $o).
% 0.54/0.74  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.54/0.74  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.54/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.74  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 0.54/0.74  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.54/0.74  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.54/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.74  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.54/0.74  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.54/0.74  thf(k6_waybel_9_type, type, k6_waybel_9: $i > $i > $i > $i > $i).
% 0.54/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.74  thf(k11_yellow_6_type, type, k11_yellow_6: $i > $i > $i).
% 0.54/0.74  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 0.54/0.74  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.54/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.74  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.54/0.74  thf(k3_waybel_2_type, type, k3_waybel_2: $i > $i > $i > $i).
% 0.54/0.74  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.54/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.74  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.54/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.74  thf(k2_yellow_6_type, type, k2_yellow_6: $i > $i > $i > $i > $i).
% 0.54/0.74  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.54/0.74  thf(dt_l1_waybel_9, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 0.54/0.74  thf('0', plain, (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.54/0.74  thf('1', plain, (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.54/0.74  thf('2', plain, (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.54/0.74  thf(d3_struct_0, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.54/0.74  thf('3', plain,
% 0.54/0.74      (![X4 : $i]:
% 0.54/0.74         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.54/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.74  thf(t26_waybel_9, conjecture,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.54/0.74         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.54/0.74         ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.54/0.74       ( ![B:$i]:
% 0.54/0.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.54/0.74             ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.54/0.74             ( l1_waybel_0 @ B @ A ) ) =>
% 0.54/0.74           ( ![C:$i]:
% 0.54/0.74             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.74               ( ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) =>
% 0.54/0.74                 ( r2_hidden @
% 0.54/0.74                   ( k12_lattice3 @ A @ C @ ( k11_yellow_6 @ A @ B ) ) @ 
% 0.54/0.74                   ( k10_yellow_6 @ A @ ( k3_waybel_2 @ A @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.54/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.74    (~( ![A:$i]:
% 0.54/0.74        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.54/0.74            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.54/0.74            ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.54/0.74          ( ![B:$i]:
% 0.54/0.74            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.54/0.74                ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.54/0.74                ( l1_waybel_0 @ B @ A ) ) =>
% 0.54/0.74              ( ![C:$i]:
% 0.54/0.74                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.74                  ( ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) =>
% 0.54/0.74                    ( r2_hidden @
% 0.54/0.74                      ( k12_lattice3 @ A @ C @ ( k11_yellow_6 @ A @ B ) ) @ 
% 0.54/0.74                      ( k10_yellow_6 @ A @ ( k3_waybel_2 @ A @ C @ B ) ) ) ) ) ) ) ) ) )),
% 0.54/0.74    inference('cnf.neg', [status(esa)], [t26_waybel_9])).
% 0.54/0.74  thf('4', plain, ((v3_yellow_6 @ sk_B @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(dt_k11_yellow_6, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.54/0.74         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.54/0.74         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.54/0.74         ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.54/0.74         ( l1_waybel_0 @ B @ A ) ) =>
% 0.54/0.74       ( m1_subset_1 @ ( k11_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.54/0.74  thf('5', plain,
% 0.54/0.74      (![X10 : $i, X11 : $i]:
% 0.54/0.74         (~ (l1_pre_topc @ X10)
% 0.54/0.74          | ~ (v8_pre_topc @ X10)
% 0.54/0.74          | ~ (v2_pre_topc @ X10)
% 0.54/0.74          | (v2_struct_0 @ X10)
% 0.54/0.74          | (v2_struct_0 @ X11)
% 0.54/0.74          | ~ (v4_orders_2 @ X11)
% 0.54/0.74          | ~ (v7_waybel_0 @ X11)
% 0.54/0.74          | ~ (v3_yellow_6 @ X11 @ X10)
% 0.54/0.74          | ~ (l1_waybel_0 @ X11 @ X10)
% 0.54/0.74          | (m1_subset_1 @ (k11_yellow_6 @ X10 @ X11) @ (u1_struct_0 @ X10)))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_k11_yellow_6])).
% 0.54/0.74  thf('6', plain,
% 0.54/0.74      (((m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.54/0.74        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.54/0.74        | ~ (v7_waybel_0 @ sk_B)
% 0.54/0.74        | ~ (v4_orders_2 @ sk_B)
% 0.54/0.74        | (v2_struct_0 @ sk_B)
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | ~ (v2_pre_topc @ sk_A)
% 0.54/0.74        | ~ (v8_pre_topc @ sk_A)
% 0.54/0.74        | ~ (l1_pre_topc @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['4', '5'])).
% 0.54/0.74  thf('7', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('8', plain, ((v7_waybel_0 @ sk_B)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('9', plain, ((v4_orders_2 @ sk_B)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('10', plain, ((v2_pre_topc @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('11', plain, ((v8_pre_topc @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('12', plain, ((l1_waybel_9 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('13', plain,
% 0.54/0.74      (![X23 : $i]: ((l1_pre_topc @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.54/0.74  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.74      inference('sup-', [status(thm)], ['12', '13'])).
% 0.54/0.74  thf('15', plain,
% 0.54/0.74      (((m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.54/0.74        | (v2_struct_0 @ sk_B)
% 0.54/0.74        | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['6', '7', '8', '9', '10', '11', '14'])).
% 0.54/0.74  thf('16', plain, (~ (v2_struct_0 @ sk_B)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('17', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | (m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.54/0.74      inference('clc', [status(thm)], ['15', '16'])).
% 0.54/0.74  thf('18', plain,
% 0.54/0.74      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.54/0.74  thf('19', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(redefinition_k12_lattice3, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.54/0.74         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.54/0.74         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.74       ( ( k12_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ B @ C ) ) ))).
% 0.54/0.74  thf('20', plain,
% 0.54/0.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.54/0.74         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.54/0.74          | ~ (l1_orders_2 @ X8)
% 0.54/0.74          | ~ (v2_lattice3 @ X8)
% 0.54/0.74          | ~ (v5_orders_2 @ X8)
% 0.54/0.74          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.54/0.74          | ((k12_lattice3 @ X8 @ X7 @ X9) = (k11_lattice3 @ X8 @ X7 @ X9)))),
% 0.54/0.74      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 0.54/0.74  thf('21', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (((k12_lattice3 @ sk_A @ sk_C @ X0)
% 0.54/0.74            = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ~ (v5_orders_2 @ sk_A)
% 0.54/0.74          | ~ (v2_lattice3 @ sk_A)
% 0.54/0.74          | ~ (l1_orders_2 @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['19', '20'])).
% 0.54/0.74  thf('22', plain, ((v5_orders_2 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('23', plain, ((v2_lattice3 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('24', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (((k12_lattice3 @ sk_A @ sk_C @ X0)
% 0.54/0.74            = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ~ (l1_orders_2 @ sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.54/0.74  thf('25', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (l1_waybel_9 @ sk_A)
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ((k12_lattice3 @ sk_A @ sk_C @ X0)
% 0.54/0.74              = (k11_lattice3 @ sk_A @ sk_C @ X0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['18', '24'])).
% 0.54/0.74  thf('26', plain, ((l1_waybel_9 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('27', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ((k12_lattice3 @ sk_A @ sk_C @ X0)
% 0.54/0.74              = (k11_lattice3 @ sk_A @ sk_C @ X0)))),
% 0.54/0.74      inference('demod', [status(thm)], ['25', '26'])).
% 0.54/0.74  thf('28', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | ((k12_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.54/0.74            = (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['17', '27'])).
% 0.54/0.74  thf('29', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | (m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.54/0.74      inference('clc', [status(thm)], ['15', '16'])).
% 0.54/0.74  thf('30', plain,
% 0.54/0.74      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.54/0.74  thf('31', plain,
% 0.54/0.74      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.54/0.74  thf('32', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(dt_k4_waybel_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.54/0.74         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.74       ( ( v1_funct_1 @ ( k4_waybel_1 @ A @ B ) ) & 
% 0.54/0.74         ( v1_funct_2 @
% 0.54/0.74           ( k4_waybel_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.54/0.74         ( m1_subset_1 @
% 0.54/0.74           ( k4_waybel_1 @ A @ B ) @ 
% 0.54/0.74           ( k1_zfmisc_1 @
% 0.54/0.74             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.54/0.74  thf('33', plain,
% 0.54/0.74      (![X21 : $i, X22 : $i]:
% 0.54/0.74         (~ (l1_orders_2 @ X21)
% 0.54/0.74          | (v2_struct_0 @ X21)
% 0.54/0.74          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.54/0.74          | (v1_funct_1 @ (k4_waybel_1 @ X21 @ X22)))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.54/0.74  thf('34', plain,
% 0.54/0.74      (((v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | ~ (l1_orders_2 @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['32', '33'])).
% 0.54/0.74  thf('35', plain,
% 0.54/0.74      ((~ (l1_waybel_9 @ sk_A)
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['31', '34'])).
% 0.54/0.74  thf('36', plain, ((l1_waybel_9 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('37', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.54/0.74      inference('demod', [status(thm)], ['35', '36'])).
% 0.54/0.74  thf('38', plain,
% 0.54/0.74      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.54/0.74  thf('39', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('40', plain,
% 0.54/0.74      (![X21 : $i, X22 : $i]:
% 0.54/0.74         (~ (l1_orders_2 @ X21)
% 0.54/0.74          | (v2_struct_0 @ X21)
% 0.54/0.74          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.54/0.74          | (v1_funct_2 @ (k4_waybel_1 @ X21 @ X22) @ (u1_struct_0 @ X21) @ 
% 0.54/0.74             (u1_struct_0 @ X21)))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.54/0.74  thf('41', plain,
% 0.54/0.74      (((v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74         (u1_struct_0 @ sk_A))
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | ~ (l1_orders_2 @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['39', '40'])).
% 0.54/0.74  thf('42', plain,
% 0.54/0.74      ((~ (l1_waybel_9 @ sk_A)
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74           (u1_struct_0 @ sk_A)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['38', '41'])).
% 0.54/0.74  thf('43', plain, ((l1_waybel_9 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('44', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74           (u1_struct_0 @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['42', '43'])).
% 0.54/0.74  thf('45', plain,
% 0.54/0.74      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.54/0.74  thf('46', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('47', plain,
% 0.54/0.74      (![X21 : $i, X22 : $i]:
% 0.54/0.74         (~ (l1_orders_2 @ X21)
% 0.54/0.74          | (v2_struct_0 @ X21)
% 0.54/0.74          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.54/0.74          | (m1_subset_1 @ (k4_waybel_1 @ X21 @ X22) @ 
% 0.54/0.74             (k1_zfmisc_1 @ 
% 0.54/0.74              (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X21)))))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.54/0.74  thf('48', plain,
% 0.54/0.74      (((m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74         (k1_zfmisc_1 @ 
% 0.54/0.74          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | ~ (l1_orders_2 @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['46', '47'])).
% 0.54/0.74  thf('49', plain,
% 0.54/0.74      ((~ (l1_waybel_9 @ sk_A)
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74           (k1_zfmisc_1 @ 
% 0.54/0.74            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['45', '48'])).
% 0.54/0.74  thf('50', plain, ((l1_waybel_9 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('51', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74           (k1_zfmisc_1 @ 
% 0.54/0.74            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.54/0.74      inference('demod', [status(thm)], ['49', '50'])).
% 0.54/0.74  thf(d18_waybel_1, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.54/0.74       ( ![B:$i]:
% 0.54/0.74         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.74           ( ![C:$i]:
% 0.54/0.74             ( ( ( v1_funct_1 @ C ) & 
% 0.54/0.74                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.54/0.74                 ( m1_subset_1 @
% 0.54/0.74                   C @ 
% 0.54/0.74                   ( k1_zfmisc_1 @
% 0.54/0.74                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.54/0.74               ( ( ( C ) = ( k4_waybel_1 @ A @ B ) ) <=>
% 0.54/0.74                 ( ![D:$i]:
% 0.54/0.74                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.74                     ( ( k3_funct_2 @
% 0.54/0.74                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ C @ D ) =
% 0.54/0.74                       ( k11_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.54/0.74  thf('52', plain,
% 0.54/0.74      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.74         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.54/0.74          | ((X19) != (k4_waybel_1 @ X18 @ X17))
% 0.54/0.74          | ((k3_funct_2 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X18) @ X19 @ 
% 0.54/0.74              X20) = (k11_lattice3 @ X18 @ X17 @ X20))
% 0.54/0.74          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.54/0.74          | ~ (m1_subset_1 @ X19 @ 
% 0.54/0.74               (k1_zfmisc_1 @ 
% 0.54/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X18))))
% 0.54/0.74          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X18))
% 0.54/0.74          | ~ (v1_funct_1 @ X19)
% 0.54/0.74          | ~ (l1_orders_2 @ X18)
% 0.54/0.74          | (v2_struct_0 @ X18))),
% 0.54/0.74      inference('cnf', [status(esa)], [d18_waybel_1])).
% 0.54/0.74  thf('53', plain,
% 0.54/0.74      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.54/0.74         ((v2_struct_0 @ X18)
% 0.54/0.74          | ~ (l1_orders_2 @ X18)
% 0.54/0.74          | ~ (v1_funct_1 @ (k4_waybel_1 @ X18 @ X17))
% 0.54/0.74          | ~ (v1_funct_2 @ (k4_waybel_1 @ X18 @ X17) @ (u1_struct_0 @ X18) @ 
% 0.54/0.74               (u1_struct_0 @ X18))
% 0.54/0.74          | ~ (m1_subset_1 @ (k4_waybel_1 @ X18 @ X17) @ 
% 0.54/0.74               (k1_zfmisc_1 @ 
% 0.54/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X18))))
% 0.54/0.74          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.54/0.74          | ((k3_funct_2 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X18) @ 
% 0.54/0.74              (k4_waybel_1 @ X18 @ X17) @ X20)
% 0.54/0.74              = (k11_lattice3 @ X18 @ X17 @ X20))
% 0.54/0.74          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18)))),
% 0.54/0.74      inference('simplify', [status(thm)], ['52'])).
% 0.54/0.74  thf('54', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v2_struct_0 @ sk_A)
% 0.54/0.74          | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.54/0.74          | ~ (l1_orders_2 @ sk_A)
% 0.54/0.74          | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['51', '53'])).
% 0.54/0.74  thf('55', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('56', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v2_struct_0 @ sk_A)
% 0.54/0.74          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.54/0.74          | ~ (l1_orders_2 @ sk_A)
% 0.54/0.74          | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['54', '55'])).
% 0.54/0.74  thf('57', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (l1_orders_2 @ sk_A)
% 0.54/0.74          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.54/0.74          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.54/0.74          | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('simplify', [status(thm)], ['56'])).
% 0.54/0.74  thf('58', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v2_struct_0 @ sk_A)
% 0.54/0.74          | (v2_struct_0 @ sk_A)
% 0.54/0.74          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.54/0.74          | ~ (l1_orders_2 @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['44', '57'])).
% 0.54/0.74  thf('59', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (l1_orders_2 @ sk_A)
% 0.54/0.74          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.54/0.74          | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('simplify', [status(thm)], ['58'])).
% 0.54/0.74  thf('60', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v2_struct_0 @ sk_A)
% 0.54/0.74          | (v2_struct_0 @ sk_A)
% 0.54/0.74          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ~ (l1_orders_2 @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['37', '59'])).
% 0.54/0.74  thf('61', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (l1_orders_2 @ sk_A)
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.54/0.74          | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('simplify', [status(thm)], ['60'])).
% 0.54/0.74  thf('62', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (l1_waybel_9 @ sk_A)
% 0.54/0.74          | (v2_struct_0 @ sk_A)
% 0.54/0.74          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['30', '61'])).
% 0.54/0.74  thf('63', plain, ((l1_waybel_9 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('64', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v2_struct_0 @ sk_A)
% 0.54/0.74          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['62', '63'])).
% 0.54/0.74  thf('65', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.54/0.74            = (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)))
% 0.54/0.74        | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['29', '64'])).
% 0.54/0.74  thf('66', plain,
% 0.54/0.74      ((((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.54/0.74          = (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)))
% 0.54/0.74        | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('simplify', [status(thm)], ['65'])).
% 0.54/0.74  thf('67', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | (m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.54/0.74      inference('clc', [status(thm)], ['15', '16'])).
% 0.54/0.74  thf('68', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.54/0.74      inference('demod', [status(thm)], ['35', '36'])).
% 0.54/0.74  thf('69', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74           (u1_struct_0 @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['42', '43'])).
% 0.54/0.74  thf('70', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74           (k1_zfmisc_1 @ 
% 0.54/0.74            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.54/0.74      inference('demod', [status(thm)], ['49', '50'])).
% 0.54/0.74  thf(redefinition_k3_funct_2, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.74     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.54/0.74         ( v1_funct_2 @ C @ A @ B ) & 
% 0.54/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.54/0.74         ( m1_subset_1 @ D @ A ) ) =>
% 0.54/0.74       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.54/0.74  thf('71', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.54/0.74          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.54/0.74          | ~ (v1_funct_1 @ X0)
% 0.54/0.74          | (v1_xboole_0 @ X1)
% 0.54/0.74          | ~ (m1_subset_1 @ X3 @ X1)
% 0.54/0.74          | ((k3_funct_2 @ X1 @ X2 @ X0 @ X3) = (k1_funct_1 @ X0 @ X3)))),
% 0.54/0.74      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.54/0.74  thf('72', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v2_struct_0 @ sk_A)
% 0.54/0.74          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.54/0.74          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['70', '71'])).
% 0.54/0.74  thf('73', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v2_struct_0 @ sk_A)
% 0.54/0.74          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.54/0.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.54/0.74          | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['69', '72'])).
% 0.54/0.74  thf('74', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74            (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74            = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.54/0.74          | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('simplify', [status(thm)], ['73'])).
% 0.54/0.74  thf('75', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v2_struct_0 @ sk_A)
% 0.54/0.74          | (v2_struct_0 @ sk_A)
% 0.54/0.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['68', '74'])).
% 0.54/0.74  thf('76', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74            (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74            = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('simplify', [status(thm)], ['75'])).
% 0.54/0.74  thf('77', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74        | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.54/0.74            = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74               (k11_yellow_6 @ sk_A @ sk_B))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['67', '76'])).
% 0.54/0.74  thf('78', plain,
% 0.54/0.74      ((((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.54/0.74          = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74             (k11_yellow_6 @ sk_A @ sk_B)))
% 0.54/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74        | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('simplify', [status(thm)], ['77'])).
% 0.54/0.74  thf('79', plain,
% 0.54/0.74      ((((k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.54/0.74          = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74             (k11_yellow_6 @ sk_A @ sk_B)))
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.74      inference('sup+', [status(thm)], ['66', '78'])).
% 0.54/0.74  thf('80', plain,
% 0.54/0.74      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | ((k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.54/0.74            = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74               (k11_yellow_6 @ sk_A @ sk_B))))),
% 0.54/0.74      inference('simplify', [status(thm)], ['79'])).
% 0.54/0.74  thf('81', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | (m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.54/0.74      inference('clc', [status(thm)], ['15', '16'])).
% 0.54/0.74  thf('82', plain,
% 0.54/0.74      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.54/0.74  thf('83', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.54/0.74      inference('demod', [status(thm)], ['35', '36'])).
% 0.54/0.74  thf('84', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74           (u1_struct_0 @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['42', '43'])).
% 0.54/0.74  thf('85', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74           (k1_zfmisc_1 @ 
% 0.54/0.74            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.54/0.74      inference('demod', [status(thm)], ['49', '50'])).
% 0.54/0.74  thf(redefinition_k2_yellow_6, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.74     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.54/0.74         ( l1_orders_2 @ B ) & ( v1_funct_1 @ C ) & 
% 0.54/0.74         ( v1_funct_2 @ C @ A @ ( u1_struct_0 @ B ) ) & 
% 0.54/0.74         ( m1_subset_1 @
% 0.54/0.74           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.54/0.74         ( m1_subset_1 @ D @ A ) ) =>
% 0.54/0.74       ( ( k2_yellow_6 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.54/0.74  thf('86', plain,
% 0.54/0.74      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.54/0.74         (~ (m1_subset_1 @ X13 @ 
% 0.54/0.74             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ (u1_struct_0 @ X15))))
% 0.54/0.74          | ~ (v1_funct_2 @ X13 @ X14 @ (u1_struct_0 @ X15))
% 0.54/0.74          | ~ (v1_funct_1 @ X13)
% 0.54/0.74          | ~ (l1_orders_2 @ X15)
% 0.54/0.74          | (v2_struct_0 @ X15)
% 0.54/0.74          | (v1_xboole_0 @ X14)
% 0.54/0.74          | ~ (m1_subset_1 @ X16 @ X14)
% 0.54/0.74          | ((k2_yellow_6 @ X14 @ X15 @ X13 @ X16) = (k1_funct_1 @ X13 @ X16)))),
% 0.54/0.74      inference('cnf', [status(esa)], [redefinition_k2_yellow_6])).
% 0.54/0.74  thf('87', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v2_struct_0 @ sk_A)
% 0.54/0.74          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | (v2_struct_0 @ sk_A)
% 0.54/0.74          | ~ (l1_orders_2 @ sk_A)
% 0.54/0.74          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.54/0.74          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['85', '86'])).
% 0.54/0.74  thf('88', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74             (u1_struct_0 @ sk_A))
% 0.54/0.74          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.54/0.74          | ~ (l1_orders_2 @ sk_A)
% 0.54/0.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.54/0.74          | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('simplify', [status(thm)], ['87'])).
% 0.54/0.74  thf('89', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v2_struct_0 @ sk_A)
% 0.54/0.74          | (v2_struct_0 @ sk_A)
% 0.54/0.74          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ~ (l1_orders_2 @ sk_A)
% 0.54/0.74          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['84', '88'])).
% 0.54/0.74  thf('90', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.54/0.74          | ~ (l1_orders_2 @ sk_A)
% 0.54/0.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.54/0.74          | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('simplify', [status(thm)], ['89'])).
% 0.54/0.74  thf('91', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v2_struct_0 @ sk_A)
% 0.54/0.74          | (v2_struct_0 @ sk_A)
% 0.54/0.74          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ~ (l1_orders_2 @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['83', '90'])).
% 0.54/0.74  thf('92', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (l1_orders_2 @ sk_A)
% 0.54/0.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.54/0.74          | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('simplify', [status(thm)], ['91'])).
% 0.54/0.74  thf('93', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (l1_waybel_9 @ sk_A)
% 0.54/0.74          | (v2_struct_0 @ sk_A)
% 0.54/0.74          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['82', '92'])).
% 0.54/0.74  thf('94', plain, ((l1_waybel_9 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('95', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v2_struct_0 @ sk_A)
% 0.54/0.74          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.54/0.74          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['93', '94'])).
% 0.54/0.74  thf('96', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74        | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.54/0.74            = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74               (k11_yellow_6 @ sk_A @ sk_B)))
% 0.54/0.74        | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['81', '95'])).
% 0.54/0.74  thf('97', plain,
% 0.54/0.74      ((((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.54/0.74          = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74             (k11_yellow_6 @ sk_A @ sk_B)))
% 0.54/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74        | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('simplify', [status(thm)], ['96'])).
% 0.54/0.74  thf('98', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('99', plain,
% 0.54/0.74      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.54/0.74  thf('100', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(t18_waybel_9, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.54/0.74       ( ![B:$i]:
% 0.54/0.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.54/0.74           ( ![C:$i]:
% 0.54/0.74             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.74               ( ( k6_waybel_9 @ A @ A @ ( k4_waybel_1 @ A @ C ) @ B ) =
% 0.54/0.74                 ( k3_waybel_2 @ A @ C @ B ) ) ) ) ) ) ))).
% 0.54/0.74  thf('101', plain,
% 0.54/0.74      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.54/0.74         ((v2_struct_0 @ X24)
% 0.54/0.74          | ~ (l1_waybel_0 @ X24 @ X25)
% 0.54/0.74          | ((k6_waybel_9 @ X25 @ X25 @ (k4_waybel_1 @ X25 @ X26) @ X24)
% 0.54/0.74              = (k3_waybel_2 @ X25 @ X26 @ X24))
% 0.54/0.74          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 0.54/0.74          | ~ (l1_orders_2 @ X25)
% 0.54/0.74          | (v2_struct_0 @ X25))),
% 0.54/0.74      inference('cnf', [status(esa)], [t18_waybel_9])).
% 0.54/0.74  thf('102', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v2_struct_0 @ sk_A)
% 0.54/0.74          | ~ (l1_orders_2 @ sk_A)
% 0.54/0.74          | ((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k3_waybel_2 @ sk_A @ sk_C @ X0))
% 0.54/0.74          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.54/0.74          | (v2_struct_0 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['100', '101'])).
% 0.54/0.74  thf('103', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (l1_waybel_9 @ sk_A)
% 0.54/0.74          | (v2_struct_0 @ X0)
% 0.54/0.74          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.54/0.74          | ((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k3_waybel_2 @ sk_A @ sk_C @ X0))
% 0.54/0.74          | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['99', '102'])).
% 0.54/0.74  thf('104', plain, ((l1_waybel_9 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('105', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v2_struct_0 @ X0)
% 0.54/0.74          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.54/0.74          | ((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.54/0.74              = (k3_waybel_2 @ sk_A @ sk_C @ X0))
% 0.54/0.74          | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['103', '104'])).
% 0.54/0.74  thf('106', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | ((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B)
% 0.54/0.74            = (k3_waybel_2 @ sk_A @ sk_C @ sk_B))
% 0.54/0.74        | (v2_struct_0 @ sk_B))),
% 0.54/0.74      inference('sup-', [status(thm)], ['98', '105'])).
% 0.54/0.74  thf('107', plain, (~ (v2_struct_0 @ sk_B)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('108', plain,
% 0.54/0.74      ((((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B)
% 0.54/0.74          = (k3_waybel_2 @ sk_A @ sk_C @ sk_B))
% 0.54/0.74        | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('clc', [status(thm)], ['106', '107'])).
% 0.54/0.74  thf('109', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('110', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.54/0.74      inference('demod', [status(thm)], ['35', '36'])).
% 0.54/0.74  thf('111', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74           (u1_struct_0 @ sk_A)))),
% 0.54/0.74      inference('demod', [status(thm)], ['42', '43'])).
% 0.54/0.74  thf('112', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74           (k1_zfmisc_1 @ 
% 0.54/0.74            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.54/0.74      inference('demod', [status(thm)], ['49', '50'])).
% 0.54/0.74  thf(t25_waybel_9, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.54/0.74         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.54/0.74         ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.54/0.74       ( ![B:$i]:
% 0.54/0.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.54/0.74             ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.54/0.74             ( l1_waybel_0 @ B @ A ) ) =>
% 0.54/0.74           ( ![C:$i]:
% 0.54/0.74             ( ( ( v1_funct_1 @ C ) & 
% 0.54/0.74                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.54/0.74                 ( m1_subset_1 @
% 0.54/0.74                   C @ 
% 0.54/0.74                   ( k1_zfmisc_1 @
% 0.54/0.74                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.54/0.74               ( ( v5_pre_topc @ C @ A @ A ) =>
% 0.54/0.74                 ( r2_hidden @
% 0.54/0.74                   ( k2_yellow_6 @
% 0.54/0.74                     ( u1_struct_0 @ A ) @ A @ C @ ( k11_yellow_6 @ A @ B ) ) @ 
% 0.54/0.74                   ( k10_yellow_6 @ A @ ( k6_waybel_9 @ A @ A @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.54/0.74  thf('113', plain,
% 0.54/0.74      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.54/0.74         ((v2_struct_0 @ X27)
% 0.54/0.74          | ~ (v4_orders_2 @ X27)
% 0.54/0.74          | ~ (v7_waybel_0 @ X27)
% 0.54/0.74          | ~ (v3_yellow_6 @ X27 @ X28)
% 0.54/0.74          | ~ (l1_waybel_0 @ X27 @ X28)
% 0.54/0.74          | ~ (v5_pre_topc @ X29 @ X28 @ X28)
% 0.54/0.74          | (r2_hidden @ 
% 0.54/0.74             (k2_yellow_6 @ (u1_struct_0 @ X28) @ X28 @ X29 @ 
% 0.54/0.74              (k11_yellow_6 @ X28 @ X27)) @ 
% 0.54/0.74             (k10_yellow_6 @ X28 @ (k6_waybel_9 @ X28 @ X28 @ X29 @ X27)))
% 0.54/0.74          | ~ (m1_subset_1 @ X29 @ 
% 0.54/0.74               (k1_zfmisc_1 @ 
% 0.54/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X28))))
% 0.54/0.74          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X28))
% 0.54/0.74          | ~ (v1_funct_1 @ X29)
% 0.54/0.74          | ~ (l1_waybel_9 @ X28)
% 0.54/0.74          | ~ (v2_lattice3 @ X28)
% 0.54/0.74          | ~ (v1_lattice3 @ X28)
% 0.54/0.74          | ~ (v5_orders_2 @ X28)
% 0.54/0.74          | ~ (v4_orders_2 @ X28)
% 0.54/0.74          | ~ (v3_orders_2 @ X28)
% 0.54/0.74          | ~ (v8_pre_topc @ X28)
% 0.54/0.74          | ~ (v2_pre_topc @ X28))),
% 0.54/0.74      inference('cnf', [status(esa)], [t25_waybel_9])).
% 0.54/0.74  thf('114', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v2_struct_0 @ sk_A)
% 0.54/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.54/0.74          | ~ (v8_pre_topc @ sk_A)
% 0.54/0.74          | ~ (v3_orders_2 @ sk_A)
% 0.54/0.74          | ~ (v4_orders_2 @ sk_A)
% 0.54/0.74          | ~ (v5_orders_2 @ sk_A)
% 0.54/0.74          | ~ (v1_lattice3 @ sk_A)
% 0.54/0.74          | ~ (v2_lattice3 @ sk_A)
% 0.54/0.74          | ~ (l1_waybel_9 @ sk_A)
% 0.54/0.74          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.54/0.74          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | (r2_hidden @ 
% 0.54/0.74             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.54/0.74             (k10_yellow_6 @ sk_A @ 
% 0.54/0.74              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.54/0.74          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_A @ sk_A)
% 0.54/0.74          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.54/0.74          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.54/0.74          | ~ (v7_waybel_0 @ X0)
% 0.54/0.74          | ~ (v4_orders_2 @ X0)
% 0.54/0.74          | (v2_struct_0 @ X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['112', '113'])).
% 0.54/0.74  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('116', plain, ((v8_pre_topc @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('117', plain, ((v3_orders_2 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('118', plain, ((v4_orders_2 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('119', plain, ((v5_orders_2 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('120', plain, ((v1_lattice3 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('121', plain, ((v2_lattice3 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('122', plain, ((l1_waybel_9 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('123', plain,
% 0.54/0.74      ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_A @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('124', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v2_struct_0 @ sk_A)
% 0.54/0.74          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.54/0.74          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.54/0.74          | (r2_hidden @ 
% 0.54/0.74             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.54/0.74             (k10_yellow_6 @ sk_A @ 
% 0.54/0.74              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.54/0.74          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.54/0.74          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.54/0.74          | ~ (v7_waybel_0 @ X0)
% 0.54/0.74          | ~ (v4_orders_2 @ X0)
% 0.54/0.74          | (v2_struct_0 @ X0))),
% 0.54/0.74      inference('demod', [status(thm)],
% 0.54/0.74                ['114', '115', '116', '117', '118', '119', '120', '121', 
% 0.54/0.74                 '122', '123'])).
% 0.54/0.74  thf('125', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v2_struct_0 @ sk_A)
% 0.54/0.74          | (v2_struct_0 @ X0)
% 0.54/0.74          | ~ (v4_orders_2 @ X0)
% 0.54/0.74          | ~ (v7_waybel_0 @ X0)
% 0.54/0.74          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.54/0.74          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.54/0.74          | (r2_hidden @ 
% 0.54/0.74             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.54/0.74             (k10_yellow_6 @ sk_A @ 
% 0.54/0.74              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.54/0.74          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.54/0.74          | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['111', '124'])).
% 0.54/0.74  thf('126', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.54/0.74          | (r2_hidden @ 
% 0.54/0.74             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.54/0.74             (k10_yellow_6 @ sk_A @ 
% 0.54/0.74              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.54/0.74          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.54/0.74          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.54/0.74          | ~ (v7_waybel_0 @ X0)
% 0.54/0.74          | ~ (v4_orders_2 @ X0)
% 0.54/0.74          | (v2_struct_0 @ X0)
% 0.54/0.74          | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('simplify', [status(thm)], ['125'])).
% 0.54/0.74  thf('127', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((v2_struct_0 @ sk_A)
% 0.54/0.74          | (v2_struct_0 @ sk_A)
% 0.54/0.74          | (v2_struct_0 @ X0)
% 0.54/0.74          | ~ (v4_orders_2 @ X0)
% 0.54/0.74          | ~ (v7_waybel_0 @ X0)
% 0.54/0.74          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.54/0.74          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.54/0.74          | (r2_hidden @ 
% 0.54/0.74             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.54/0.74             (k10_yellow_6 @ sk_A @ 
% 0.54/0.74              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['110', '126'])).
% 0.54/0.74  thf('128', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((r2_hidden @ 
% 0.54/0.74           (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.54/0.74           (k10_yellow_6 @ sk_A @ 
% 0.54/0.74            (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.54/0.74          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.54/0.74          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.54/0.74          | ~ (v7_waybel_0 @ X0)
% 0.54/0.74          | ~ (v4_orders_2 @ X0)
% 0.54/0.74          | (v2_struct_0 @ X0)
% 0.54/0.74          | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('simplify', [status(thm)], ['127'])).
% 0.54/0.74  thf('129', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | (v2_struct_0 @ sk_B)
% 0.54/0.74        | ~ (v4_orders_2 @ sk_B)
% 0.54/0.74        | ~ (v7_waybel_0 @ sk_B)
% 0.54/0.74        | ~ (v3_yellow_6 @ sk_B @ sk_A)
% 0.54/0.74        | (r2_hidden @ 
% 0.54/0.74           (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.54/0.74           (k10_yellow_6 @ sk_A @ 
% 0.54/0.74            (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['109', '128'])).
% 0.54/0.74  thf('130', plain, ((v4_orders_2 @ sk_B)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('131', plain, ((v7_waybel_0 @ sk_B)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('132', plain, ((v3_yellow_6 @ sk_B @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('133', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | (v2_struct_0 @ sk_B)
% 0.54/0.74        | (r2_hidden @ 
% 0.54/0.74           (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.54/0.74           (k10_yellow_6 @ sk_A @ 
% 0.54/0.74            (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B))))),
% 0.54/0.74      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 0.54/0.74  thf('134', plain, (~ (v2_struct_0 @ sk_B)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('135', plain,
% 0.54/0.74      (((r2_hidden @ 
% 0.54/0.74         (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.54/0.74         (k10_yellow_6 @ sk_A @ 
% 0.54/0.74          (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B)))
% 0.54/0.74        | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('clc', [status(thm)], ['133', '134'])).
% 0.54/0.74  thf('136', plain,
% 0.54/0.74      (((r2_hidden @ 
% 0.54/0.74         (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.54/0.74         (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('sup+', [status(thm)], ['108', '135'])).
% 0.54/0.74  thf('137', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A)
% 0.54/0.74        | (r2_hidden @ 
% 0.54/0.74           (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.54/0.74            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.54/0.74           (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B))))),
% 0.54/0.74      inference('simplify', [status(thm)], ['136'])).
% 0.54/0.74  thf('138', plain,
% 0.54/0.74      (((r2_hidden @ 
% 0.54/0.74         (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74          (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.54/0.74         (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74        | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('sup+', [status(thm)], ['97', '137'])).
% 0.54/0.74  thf('139', plain,
% 0.54/0.74      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | (r2_hidden @ 
% 0.54/0.74           (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.54/0.74            (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.54/0.74           (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B))))),
% 0.54/0.74      inference('simplify', [status(thm)], ['138'])).
% 0.54/0.74  thf('140', plain,
% 0.54/0.74      (((r2_hidden @ 
% 0.54/0.74         (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.54/0.74         (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.74      inference('sup+', [status(thm)], ['80', '139'])).
% 0.54/0.74  thf('141', plain,
% 0.54/0.74      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | (r2_hidden @ 
% 0.54/0.74           (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.54/0.74           (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B))))),
% 0.54/0.74      inference('simplify', [status(thm)], ['140'])).
% 0.54/0.74  thf('142', plain,
% 0.54/0.74      (((r2_hidden @ 
% 0.54/0.74         (k12_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.54/0.74         (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.74      inference('sup+', [status(thm)], ['28', '141'])).
% 0.54/0.74  thf('143', plain,
% 0.54/0.74      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.54/0.74        | (v2_struct_0 @ sk_A)
% 0.54/0.74        | (r2_hidden @ 
% 0.54/0.74           (k12_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.54/0.74           (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B))))),
% 0.54/0.74      inference('simplify', [status(thm)], ['142'])).
% 0.54/0.74  thf('144', plain,
% 0.54/0.74      (~ (r2_hidden @ 
% 0.54/0.74          (k12_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.54/0.74          (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('145', plain,
% 0.54/0.74      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.74      inference('clc', [status(thm)], ['143', '144'])).
% 0.54/0.74  thf('146', plain,
% 0.54/0.74      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.54/0.74        | ~ (l1_struct_0 @ sk_A)
% 0.54/0.74        | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('sup+', [status(thm)], ['3', '145'])).
% 0.54/0.74  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.74      inference('sup-', [status(thm)], ['12', '13'])).
% 0.54/0.74  thf(dt_l1_pre_topc, axiom,
% 0.54/0.74    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.54/0.74  thf('148', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.54/0.74  thf('149', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.74      inference('sup-', [status(thm)], ['147', '148'])).
% 0.54/0.74  thf('150', plain,
% 0.54/0.74      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['146', '149'])).
% 0.54/0.74  thf(cc1_lattice3, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( l1_orders_2 @ A ) =>
% 0.54/0.74       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.54/0.74  thf('151', plain,
% 0.54/0.74      (![X6 : $i]:
% 0.54/0.74         (~ (v1_lattice3 @ X6) | ~ (v2_struct_0 @ X6) | ~ (l1_orders_2 @ X6))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.54/0.74  thf('152', plain,
% 0.54/0.74      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.54/0.74        | ~ (l1_orders_2 @ sk_A)
% 0.54/0.74        | ~ (v1_lattice3 @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['150', '151'])).
% 0.54/0.74  thf('153', plain, ((v1_lattice3 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('154', plain,
% 0.54/0.74      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | ~ (l1_orders_2 @ sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['152', '153'])).
% 0.54/0.74  thf('155', plain,
% 0.54/0.74      ((~ (l1_waybel_9 @ sk_A) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['2', '154'])).
% 0.54/0.74  thf('156', plain, ((l1_waybel_9 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('157', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['155', '156'])).
% 0.54/0.74  thf(fc2_yellow_0, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.54/0.74       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.54/0.74  thf('158', plain,
% 0.54/0.74      (![X12 : $i]:
% 0.54/0.74         (~ (v1_xboole_0 @ (k2_struct_0 @ X12))
% 0.54/0.74          | ~ (l1_orders_2 @ X12)
% 0.54/0.74          | (v2_struct_0 @ X12))),
% 0.54/0.74      inference('cnf', [status(esa)], [fc2_yellow_0])).
% 0.54/0.74  thf('159', plain, (((v2_struct_0 @ sk_A) | ~ (l1_orders_2 @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['157', '158'])).
% 0.54/0.74  thf('160', plain, ((~ (l1_waybel_9 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['1', '159'])).
% 0.54/0.74  thf('161', plain, ((l1_waybel_9 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('162', plain, ((v2_struct_0 @ sk_A)),
% 0.54/0.74      inference('demod', [status(thm)], ['160', '161'])).
% 0.54/0.74  thf('163', plain,
% 0.54/0.74      (![X6 : $i]:
% 0.54/0.74         (~ (v1_lattice3 @ X6) | ~ (v2_struct_0 @ X6) | ~ (l1_orders_2 @ X6))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.54/0.74  thf('164', plain, ((~ (l1_orders_2 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['162', '163'])).
% 0.54/0.74  thf('165', plain, ((v1_lattice3 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('166', plain, (~ (l1_orders_2 @ sk_A)),
% 0.54/0.74      inference('demod', [status(thm)], ['164', '165'])).
% 0.54/0.74  thf('167', plain, (~ (l1_waybel_9 @ sk_A)),
% 0.54/0.74      inference('sup-', [status(thm)], ['0', '166'])).
% 0.54/0.74  thf('168', plain, ((l1_waybel_9 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('169', plain, ($false), inference('demod', [status(thm)], ['167', '168'])).
% 0.54/0.74  
% 0.54/0.74  % SZS output end Refutation
% 0.54/0.74  
% 0.54/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
