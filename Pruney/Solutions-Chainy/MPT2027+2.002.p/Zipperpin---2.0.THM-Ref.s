%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X070uHsnez

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:30 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 530 expanded)
%              Number of leaves         :   52 ( 177 expanded)
%              Depth                    :   36
%              Number of atoms          : 2727 (12834 expanded)
%              Number of equality atoms :   55 (  55 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k3_waybel_2_type,type,(
    k3_waybel_2: $i > $i > $i > $i )).

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
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X23: $i] :
      ( ( l1_orders_2 @ X23 )
      | ~ ( l1_waybel_9 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('149',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ X0 )
      | ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['147','150'])).

thf('152',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['146','151'])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('153',plain,(
    ! [X6: $i] :
      ( ~ ( v1_lattice3 @ X6 )
      | ~ ( v2_struct_0 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('154',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','156'])).

thf('158',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['157','158'])).

thf(fc2_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('160',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_yellow_0])).

thf('161',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','161'])).

thf('163',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X6: $i] :
      ( ~ ( v1_lattice3 @ X6 )
      | ~ ( v2_struct_0 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('166',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','168'])).

thf('170',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    $false ),
    inference(demod,[status(thm)],['169','170'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X070uHsnez
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.77  % Solved by: fo/fo7.sh
% 0.55/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.77  % done 463 iterations in 0.312s
% 0.55/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.77  % SZS output start Refutation
% 0.55/0.77  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.55/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.77  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.55/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.77  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.55/0.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.55/0.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.77  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.55/0.77  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.55/0.77  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.55/0.77  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.55/0.77  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.55/0.77  thf(v3_yellow_6_type, type, v3_yellow_6: $i > $i > $o).
% 0.55/0.77  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.55/0.77  thf(k12_lattice3_type, type, k12_lattice3: $i > $i > $i > $i).
% 0.55/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.77  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 0.55/0.77  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.55/0.77  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.55/0.77  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.55/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.77  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.55/0.77  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.55/0.77  thf(k6_waybel_9_type, type, k6_waybel_9: $i > $i > $i > $i > $i).
% 0.55/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.77  thf(k11_yellow_6_type, type, k11_yellow_6: $i > $i > $i).
% 0.55/0.77  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 0.55/0.77  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.55/0.77  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.55/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.77  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.55/0.77  thf(k3_waybel_2_type, type, k3_waybel_2: $i > $i > $i > $i).
% 0.55/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.77  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.55/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.77  thf(k2_yellow_6_type, type, k2_yellow_6: $i > $i > $i > $i > $i).
% 0.55/0.77  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.55/0.77  thf(dt_l1_waybel_9, axiom,
% 0.55/0.77    (![A:$i]:
% 0.55/0.77     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 0.55/0.77  thf('0', plain, (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.55/0.77  thf('1', plain, (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.55/0.77  thf('2', plain, (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.55/0.77  thf(d3_struct_0, axiom,
% 0.55/0.77    (![A:$i]:
% 0.55/0.77     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.55/0.77  thf('3', plain,
% 0.55/0.77      (![X4 : $i]:
% 0.55/0.77         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.55/0.77      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.77  thf(t26_waybel_9, conjecture,
% 0.55/0.77    (![A:$i]:
% 0.55/0.77     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.55/0.77         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.55/0.77         ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.55/0.77       ( ![B:$i]:
% 0.55/0.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.55/0.77             ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.55/0.77             ( l1_waybel_0 @ B @ A ) ) =>
% 0.55/0.77           ( ![C:$i]:
% 0.55/0.77             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.77               ( ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) =>
% 0.55/0.77                 ( r2_hidden @
% 0.55/0.77                   ( k12_lattice3 @ A @ C @ ( k11_yellow_6 @ A @ B ) ) @ 
% 0.55/0.77                   ( k10_yellow_6 @ A @ ( k3_waybel_2 @ A @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.55/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.77    (~( ![A:$i]:
% 0.55/0.77        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.55/0.77            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.55/0.77            ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.55/0.77          ( ![B:$i]:
% 0.55/0.77            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.55/0.77                ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.55/0.77                ( l1_waybel_0 @ B @ A ) ) =>
% 0.55/0.77              ( ![C:$i]:
% 0.55/0.77                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.77                  ( ( v5_pre_topc @ ( k4_waybel_1 @ A @ C ) @ A @ A ) =>
% 0.55/0.77                    ( r2_hidden @
% 0.55/0.77                      ( k12_lattice3 @ A @ C @ ( k11_yellow_6 @ A @ B ) ) @ 
% 0.55/0.77                      ( k10_yellow_6 @ A @ ( k3_waybel_2 @ A @ C @ B ) ) ) ) ) ) ) ) ) )),
% 0.55/0.77    inference('cnf.neg', [status(esa)], [t26_waybel_9])).
% 0.55/0.77  thf('4', plain, ((v3_yellow_6 @ sk_B @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf(dt_k11_yellow_6, axiom,
% 0.55/0.77    (![A:$i,B:$i]:
% 0.55/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.55/0.77         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.55/0.77         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.55/0.77         ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.55/0.77         ( l1_waybel_0 @ B @ A ) ) =>
% 0.55/0.77       ( m1_subset_1 @ ( k11_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.55/0.77  thf('5', plain,
% 0.55/0.77      (![X10 : $i, X11 : $i]:
% 0.55/0.77         (~ (l1_pre_topc @ X10)
% 0.55/0.77          | ~ (v8_pre_topc @ X10)
% 0.55/0.77          | ~ (v2_pre_topc @ X10)
% 0.55/0.77          | (v2_struct_0 @ X10)
% 0.55/0.77          | (v2_struct_0 @ X11)
% 0.55/0.77          | ~ (v4_orders_2 @ X11)
% 0.55/0.77          | ~ (v7_waybel_0 @ X11)
% 0.55/0.77          | ~ (v3_yellow_6 @ X11 @ X10)
% 0.55/0.77          | ~ (l1_waybel_0 @ X11 @ X10)
% 0.55/0.77          | (m1_subset_1 @ (k11_yellow_6 @ X10 @ X11) @ (u1_struct_0 @ X10)))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k11_yellow_6])).
% 0.55/0.77  thf('6', plain,
% 0.55/0.77      (((m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.55/0.77        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.55/0.77        | ~ (v7_waybel_0 @ sk_B)
% 0.55/0.77        | ~ (v4_orders_2 @ sk_B)
% 0.55/0.77        | (v2_struct_0 @ sk_B)
% 0.55/0.77        | (v2_struct_0 @ sk_A)
% 0.55/0.77        | ~ (v2_pre_topc @ sk_A)
% 0.55/0.77        | ~ (v8_pre_topc @ sk_A)
% 0.55/0.77        | ~ (l1_pre_topc @ sk_A))),
% 0.55/0.77      inference('sup-', [status(thm)], ['4', '5'])).
% 0.55/0.77  thf('7', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('8', plain, ((v7_waybel_0 @ sk_B)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('9', plain, ((v4_orders_2 @ sk_B)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('10', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('11', plain, ((v8_pre_topc @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('12', plain, ((l1_waybel_9 @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('13', plain,
% 0.55/0.77      (![X23 : $i]: ((l1_pre_topc @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.55/0.77  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.77      inference('sup-', [status(thm)], ['12', '13'])).
% 0.55/0.77  thf('15', plain,
% 0.55/0.77      (((m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.55/0.77        | (v2_struct_0 @ sk_B)
% 0.55/0.77        | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('demod', [status(thm)], ['6', '7', '8', '9', '10', '11', '14'])).
% 0.55/0.77  thf('16', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('17', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A)
% 0.55/0.77        | (m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.55/0.77      inference('clc', [status(thm)], ['15', '16'])).
% 0.55/0.77  thf('18', plain,
% 0.55/0.77      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.55/0.77  thf('19', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf(redefinition_k12_lattice3, axiom,
% 0.55/0.77    (![A:$i,B:$i,C:$i]:
% 0.55/0.77     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.55/0.77         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.55/0.77         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.77       ( ( k12_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ B @ C ) ) ))).
% 0.55/0.77  thf('20', plain,
% 0.55/0.77      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.55/0.77         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.55/0.77          | ~ (l1_orders_2 @ X8)
% 0.55/0.77          | ~ (v2_lattice3 @ X8)
% 0.55/0.77          | ~ (v5_orders_2 @ X8)
% 0.55/0.77          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.55/0.77          | ((k12_lattice3 @ X8 @ X7 @ X9) = (k11_lattice3 @ X8 @ X7 @ X9)))),
% 0.55/0.77      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 0.55/0.77  thf('21', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (((k12_lattice3 @ sk_A @ sk_C @ X0)
% 0.55/0.77            = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ~ (v5_orders_2 @ sk_A)
% 0.55/0.77          | ~ (v2_lattice3 @ sk_A)
% 0.55/0.77          | ~ (l1_orders_2 @ sk_A))),
% 0.55/0.77      inference('sup-', [status(thm)], ['19', '20'])).
% 0.55/0.77  thf('22', plain, ((v5_orders_2 @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('23', plain, ((v2_lattice3 @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('24', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (((k12_lattice3 @ sk_A @ sk_C @ X0)
% 0.55/0.77            = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ~ (l1_orders_2 @ sk_A))),
% 0.55/0.77      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.55/0.77  thf('25', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (l1_waybel_9 @ sk_A)
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ((k12_lattice3 @ sk_A @ sk_C @ X0)
% 0.55/0.77              = (k11_lattice3 @ sk_A @ sk_C @ X0)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['18', '24'])).
% 0.55/0.77  thf('26', plain, ((l1_waybel_9 @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('27', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ((k12_lattice3 @ sk_A @ sk_C @ X0)
% 0.55/0.77              = (k11_lattice3 @ sk_A @ sk_C @ X0)))),
% 0.55/0.77      inference('demod', [status(thm)], ['25', '26'])).
% 0.55/0.77  thf('28', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A)
% 0.55/0.77        | ((k12_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.55/0.77            = (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['17', '27'])).
% 0.55/0.77  thf('29', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A)
% 0.55/0.77        | (m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.55/0.77      inference('clc', [status(thm)], ['15', '16'])).
% 0.55/0.77  thf('30', plain,
% 0.55/0.77      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.55/0.77  thf('31', plain,
% 0.55/0.77      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.55/0.77  thf('32', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf(dt_k4_waybel_1, axiom,
% 0.55/0.77    (![A:$i,B:$i]:
% 0.55/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.55/0.77         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.77       ( ( v1_funct_1 @ ( k4_waybel_1 @ A @ B ) ) & 
% 0.55/0.77         ( v1_funct_2 @
% 0.55/0.77           ( k4_waybel_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.55/0.77         ( m1_subset_1 @
% 0.55/0.77           ( k4_waybel_1 @ A @ B ) @ 
% 0.55/0.77           ( k1_zfmisc_1 @
% 0.55/0.77             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.55/0.77  thf('33', plain,
% 0.55/0.77      (![X21 : $i, X22 : $i]:
% 0.55/0.77         (~ (l1_orders_2 @ X21)
% 0.55/0.77          | (v2_struct_0 @ X21)
% 0.55/0.77          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.55/0.77          | (v1_funct_1 @ (k4_waybel_1 @ X21 @ X22)))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.55/0.77  thf('34', plain,
% 0.55/0.77      (((v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.55/0.77        | (v2_struct_0 @ sk_A)
% 0.55/0.77        | ~ (l1_orders_2 @ sk_A))),
% 0.55/0.77      inference('sup-', [status(thm)], ['32', '33'])).
% 0.55/0.77  thf('35', plain,
% 0.55/0.77      ((~ (l1_waybel_9 @ sk_A)
% 0.55/0.77        | (v2_struct_0 @ sk_A)
% 0.55/0.77        | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['31', '34'])).
% 0.55/0.77  thf('36', plain, ((l1_waybel_9 @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('37', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.55/0.77      inference('demod', [status(thm)], ['35', '36'])).
% 0.55/0.77  thf('38', plain,
% 0.55/0.77      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.55/0.77  thf('39', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('40', plain,
% 0.55/0.77      (![X21 : $i, X22 : $i]:
% 0.55/0.77         (~ (l1_orders_2 @ X21)
% 0.55/0.77          | (v2_struct_0 @ X21)
% 0.55/0.77          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.55/0.77          | (v1_funct_2 @ (k4_waybel_1 @ X21 @ X22) @ (u1_struct_0 @ X21) @ 
% 0.55/0.77             (u1_struct_0 @ X21)))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.55/0.77  thf('41', plain,
% 0.55/0.77      (((v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77         (u1_struct_0 @ sk_A))
% 0.55/0.77        | (v2_struct_0 @ sk_A)
% 0.55/0.77        | ~ (l1_orders_2 @ sk_A))),
% 0.55/0.77      inference('sup-', [status(thm)], ['39', '40'])).
% 0.55/0.77  thf('42', plain,
% 0.55/0.77      ((~ (l1_waybel_9 @ sk_A)
% 0.55/0.77        | (v2_struct_0 @ sk_A)
% 0.55/0.77        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77           (u1_struct_0 @ sk_A)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['38', '41'])).
% 0.55/0.77  thf('43', plain, ((l1_waybel_9 @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('44', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A)
% 0.55/0.77        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77           (u1_struct_0 @ sk_A)))),
% 0.55/0.77      inference('demod', [status(thm)], ['42', '43'])).
% 0.55/0.77  thf('45', plain,
% 0.55/0.77      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.55/0.77  thf('46', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('47', plain,
% 0.55/0.77      (![X21 : $i, X22 : $i]:
% 0.55/0.77         (~ (l1_orders_2 @ X21)
% 0.55/0.77          | (v2_struct_0 @ X21)
% 0.55/0.77          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.55/0.77          | (m1_subset_1 @ (k4_waybel_1 @ X21 @ X22) @ 
% 0.55/0.77             (k1_zfmisc_1 @ 
% 0.55/0.77              (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X21)))))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_k4_waybel_1])).
% 0.55/0.77  thf('48', plain,
% 0.55/0.77      (((m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.77         (k1_zfmisc_1 @ 
% 0.55/0.77          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.55/0.77        | (v2_struct_0 @ sk_A)
% 0.55/0.77        | ~ (l1_orders_2 @ sk_A))),
% 0.55/0.77      inference('sup-', [status(thm)], ['46', '47'])).
% 0.55/0.77  thf('49', plain,
% 0.55/0.77      ((~ (l1_waybel_9 @ sk_A)
% 0.55/0.77        | (v2_struct_0 @ sk_A)
% 0.55/0.77        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.77           (k1_zfmisc_1 @ 
% 0.55/0.77            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['45', '48'])).
% 0.55/0.77  thf('50', plain, ((l1_waybel_9 @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('51', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A)
% 0.55/0.77        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.77           (k1_zfmisc_1 @ 
% 0.55/0.77            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.55/0.77      inference('demod', [status(thm)], ['49', '50'])).
% 0.55/0.77  thf(d18_waybel_1, axiom,
% 0.55/0.77    (![A:$i]:
% 0.55/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.55/0.77       ( ![B:$i]:
% 0.55/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.77           ( ![C:$i]:
% 0.55/0.77             ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.77                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.55/0.77                 ( m1_subset_1 @
% 0.55/0.77                   C @ 
% 0.55/0.77                   ( k1_zfmisc_1 @
% 0.55/0.77                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.55/0.77               ( ( ( C ) = ( k4_waybel_1 @ A @ B ) ) <=>
% 0.55/0.77                 ( ![D:$i]:
% 0.55/0.77                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.77                     ( ( k3_funct_2 @
% 0.55/0.77                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ C @ D ) =
% 0.55/0.77                       ( k11_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.77  thf('52', plain,
% 0.55/0.77      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.55/0.77         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.55/0.77          | ((X19) != (k4_waybel_1 @ X18 @ X17))
% 0.55/0.77          | ((k3_funct_2 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X18) @ X19 @ 
% 0.55/0.77              X20) = (k11_lattice3 @ X18 @ X17 @ X20))
% 0.55/0.77          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.55/0.77          | ~ (m1_subset_1 @ X19 @ 
% 0.55/0.77               (k1_zfmisc_1 @ 
% 0.55/0.77                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X18))))
% 0.55/0.77          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X18))
% 0.55/0.77          | ~ (v1_funct_1 @ X19)
% 0.55/0.77          | ~ (l1_orders_2 @ X18)
% 0.55/0.77          | (v2_struct_0 @ X18))),
% 0.55/0.77      inference('cnf', [status(esa)], [d18_waybel_1])).
% 0.55/0.77  thf('53', plain,
% 0.55/0.77      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.55/0.77         ((v2_struct_0 @ X18)
% 0.55/0.77          | ~ (l1_orders_2 @ X18)
% 0.55/0.77          | ~ (v1_funct_1 @ (k4_waybel_1 @ X18 @ X17))
% 0.55/0.77          | ~ (v1_funct_2 @ (k4_waybel_1 @ X18 @ X17) @ (u1_struct_0 @ X18) @ 
% 0.55/0.77               (u1_struct_0 @ X18))
% 0.55/0.77          | ~ (m1_subset_1 @ (k4_waybel_1 @ X18 @ X17) @ 
% 0.55/0.77               (k1_zfmisc_1 @ 
% 0.55/0.77                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X18))))
% 0.55/0.77          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.55/0.77          | ((k3_funct_2 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X18) @ 
% 0.55/0.77              (k4_waybel_1 @ X18 @ X17) @ X20)
% 0.55/0.77              = (k11_lattice3 @ X18 @ X17 @ X20))
% 0.55/0.77          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18)))),
% 0.55/0.77      inference('simplify', [status(thm)], ['52'])).
% 0.55/0.77  thf('54', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((v2_struct_0 @ sk_A)
% 0.55/0.77          | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.77               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.55/0.77          | ~ (l1_orders_2 @ sk_A)
% 0.55/0.77          | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('sup-', [status(thm)], ['51', '53'])).
% 0.55/0.77  thf('55', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('56', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((v2_struct_0 @ sk_A)
% 0.55/0.77          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.77               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.55/0.77          | ~ (l1_orders_2 @ sk_A)
% 0.55/0.77          | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('demod', [status(thm)], ['54', '55'])).
% 0.55/0.77  thf('57', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (l1_orders_2 @ sk_A)
% 0.55/0.77          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.55/0.77          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.77               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.55/0.77          | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('simplify', [status(thm)], ['56'])).
% 0.55/0.77  thf('58', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((v2_struct_0 @ sk_A)
% 0.55/0.77          | (v2_struct_0 @ sk_A)
% 0.55/0.77          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.55/0.77          | ~ (l1_orders_2 @ sk_A))),
% 0.55/0.77      inference('sup-', [status(thm)], ['44', '57'])).
% 0.55/0.77  thf('59', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (l1_orders_2 @ sk_A)
% 0.55/0.77          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.55/0.77          | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('simplify', [status(thm)], ['58'])).
% 0.55/0.77  thf('60', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((v2_struct_0 @ sk_A)
% 0.55/0.77          | (v2_struct_0 @ sk_A)
% 0.55/0.77          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ~ (l1_orders_2 @ sk_A))),
% 0.55/0.77      inference('sup-', [status(thm)], ['37', '59'])).
% 0.55/0.77  thf('61', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (l1_orders_2 @ sk_A)
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.55/0.77          | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('simplify', [status(thm)], ['60'])).
% 0.55/0.77  thf('62', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (l1_waybel_9 @ sk_A)
% 0.55/0.77          | (v2_struct_0 @ sk_A)
% 0.55/0.77          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['30', '61'])).
% 0.55/0.77  thf('63', plain, ((l1_waybel_9 @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('64', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((v2_struct_0 @ sk_A)
% 0.55/0.77          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k11_lattice3 @ sk_A @ sk_C @ X0))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.77      inference('demod', [status(thm)], ['62', '63'])).
% 0.55/0.77  thf('65', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A)
% 0.55/0.77        | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.55/0.77            = (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)))
% 0.55/0.77        | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('sup-', [status(thm)], ['29', '64'])).
% 0.55/0.77  thf('66', plain,
% 0.55/0.77      ((((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.55/0.77          = (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)))
% 0.55/0.77        | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('simplify', [status(thm)], ['65'])).
% 0.55/0.77  thf('67', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A)
% 0.55/0.77        | (m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.55/0.77      inference('clc', [status(thm)], ['15', '16'])).
% 0.55/0.77  thf('68', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.55/0.77      inference('demod', [status(thm)], ['35', '36'])).
% 0.55/0.77  thf('69', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A)
% 0.55/0.77        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77           (u1_struct_0 @ sk_A)))),
% 0.55/0.77      inference('demod', [status(thm)], ['42', '43'])).
% 0.55/0.77  thf('70', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A)
% 0.55/0.77        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.77           (k1_zfmisc_1 @ 
% 0.55/0.77            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.55/0.77      inference('demod', [status(thm)], ['49', '50'])).
% 0.55/0.77  thf(redefinition_k3_funct_2, axiom,
% 0.55/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.77     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.55/0.77         ( v1_funct_2 @ C @ A @ B ) & 
% 0.55/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.55/0.77         ( m1_subset_1 @ D @ A ) ) =>
% 0.55/0.77       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.55/0.77  thf('71', plain,
% 0.55/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.55/0.77         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.55/0.77          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.55/0.77          | ~ (v1_funct_1 @ X0)
% 0.55/0.77          | (v1_xboole_0 @ X1)
% 0.55/0.77          | ~ (m1_subset_1 @ X3 @ X1)
% 0.55/0.77          | ((k3_funct_2 @ X1 @ X2 @ X0 @ X3) = (k1_funct_1 @ X0 @ X3)))),
% 0.55/0.77      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.55/0.77  thf('72', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((v2_struct_0 @ sk_A)
% 0.55/0.77          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.55/0.77          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.77               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['70', '71'])).
% 0.55/0.77  thf('73', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((v2_struct_0 @ sk_A)
% 0.55/0.77          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.55/0.77          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.55/0.77          | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('sup-', [status(thm)], ['69', '72'])).
% 0.55/0.77  thf('74', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77            (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77            = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.55/0.77          | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('simplify', [status(thm)], ['73'])).
% 0.55/0.77  thf('75', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((v2_struct_0 @ sk_A)
% 0.55/0.77          | (v2_struct_0 @ sk_A)
% 0.55/0.77          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['68', '74'])).
% 0.55/0.77  thf('76', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77            (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77            = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('simplify', [status(thm)], ['75'])).
% 0.55/0.77  thf('77', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A)
% 0.55/0.77        | (v2_struct_0 @ sk_A)
% 0.55/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77        | ((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.55/0.77            = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.77               (k11_yellow_6 @ sk_A @ sk_B))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['67', '76'])).
% 0.55/0.77  thf('78', plain,
% 0.55/0.77      ((((k3_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.55/0.77          = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.77             (k11_yellow_6 @ sk_A @ sk_B)))
% 0.55/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77        | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('simplify', [status(thm)], ['77'])).
% 0.55/0.77  thf('79', plain,
% 0.55/0.77      ((((k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.55/0.77          = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.77             (k11_yellow_6 @ sk_A @ sk_B)))
% 0.55/0.77        | (v2_struct_0 @ sk_A)
% 0.55/0.77        | (v2_struct_0 @ sk_A)
% 0.55/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.77      inference('sup+', [status(thm)], ['66', '78'])).
% 0.55/0.77  thf('80', plain,
% 0.55/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77        | (v2_struct_0 @ sk_A)
% 0.55/0.77        | ((k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.55/0.77            = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.77               (k11_yellow_6 @ sk_A @ sk_B))))),
% 0.55/0.77      inference('simplify', [status(thm)], ['79'])).
% 0.55/0.77  thf('81', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A)
% 0.55/0.77        | (m1_subset_1 @ (k11_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.55/0.77      inference('clc', [status(thm)], ['15', '16'])).
% 0.55/0.77  thf('82', plain,
% 0.55/0.77      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.55/0.77  thf('83', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.55/0.77      inference('demod', [status(thm)], ['35', '36'])).
% 0.55/0.77  thf('84', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A)
% 0.55/0.77        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77           (u1_struct_0 @ sk_A)))),
% 0.55/0.77      inference('demod', [status(thm)], ['42', '43'])).
% 0.55/0.77  thf('85', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A)
% 0.55/0.77        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.77           (k1_zfmisc_1 @ 
% 0.55/0.77            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.55/0.77      inference('demod', [status(thm)], ['49', '50'])).
% 0.55/0.77  thf(redefinition_k2_yellow_6, axiom,
% 0.55/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.77     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.55/0.77         ( l1_orders_2 @ B ) & ( v1_funct_1 @ C ) & 
% 0.55/0.77         ( v1_funct_2 @ C @ A @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.77         ( m1_subset_1 @
% 0.55/0.77           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.55/0.77         ( m1_subset_1 @ D @ A ) ) =>
% 0.55/0.77       ( ( k2_yellow_6 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.55/0.77  thf('86', plain,
% 0.55/0.77      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.55/0.77         (~ (m1_subset_1 @ X13 @ 
% 0.55/0.77             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ (u1_struct_0 @ X15))))
% 0.55/0.77          | ~ (v1_funct_2 @ X13 @ X14 @ (u1_struct_0 @ X15))
% 0.55/0.77          | ~ (v1_funct_1 @ X13)
% 0.55/0.77          | ~ (l1_orders_2 @ X15)
% 0.55/0.77          | (v2_struct_0 @ X15)
% 0.55/0.77          | (v1_xboole_0 @ X14)
% 0.55/0.77          | ~ (m1_subset_1 @ X16 @ X14)
% 0.55/0.77          | ((k2_yellow_6 @ X14 @ X15 @ X13 @ X16) = (k1_funct_1 @ X13 @ X16)))),
% 0.55/0.77      inference('cnf', [status(esa)], [redefinition_k2_yellow_6])).
% 0.55/0.77  thf('87', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((v2_struct_0 @ sk_A)
% 0.55/0.77          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | (v2_struct_0 @ sk_A)
% 0.55/0.77          | ~ (l1_orders_2 @ sk_A)
% 0.55/0.77          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.55/0.77          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.77               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['85', '86'])).
% 0.55/0.77  thf('88', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77             (u1_struct_0 @ sk_A))
% 0.55/0.77          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.55/0.77          | ~ (l1_orders_2 @ sk_A)
% 0.55/0.77          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.55/0.77          | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('simplify', [status(thm)], ['87'])).
% 0.55/0.77  thf('89', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((v2_struct_0 @ sk_A)
% 0.55/0.77          | (v2_struct_0 @ sk_A)
% 0.55/0.77          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ~ (l1_orders_2 @ sk_A)
% 0.55/0.77          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['84', '88'])).
% 0.55/0.77  thf('90', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.55/0.77          | ~ (l1_orders_2 @ sk_A)
% 0.55/0.77          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.55/0.77          | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('simplify', [status(thm)], ['89'])).
% 0.55/0.77  thf('91', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((v2_struct_0 @ sk_A)
% 0.55/0.77          | (v2_struct_0 @ sk_A)
% 0.55/0.77          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ~ (l1_orders_2 @ sk_A))),
% 0.55/0.77      inference('sup-', [status(thm)], ['83', '90'])).
% 0.55/0.77  thf('92', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (l1_orders_2 @ sk_A)
% 0.55/0.77          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.55/0.77          | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('simplify', [status(thm)], ['91'])).
% 0.55/0.77  thf('93', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (l1_waybel_9 @ sk_A)
% 0.55/0.77          | (v2_struct_0 @ sk_A)
% 0.55/0.77          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['82', '92'])).
% 0.55/0.77  thf('94', plain, ((l1_waybel_9 @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('95', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((v2_struct_0 @ sk_A)
% 0.55/0.77          | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))
% 0.55/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.77      inference('demod', [status(thm)], ['93', '94'])).
% 0.55/0.77  thf('96', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A)
% 0.55/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77        | ((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.77            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.55/0.77            = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.77               (k11_yellow_6 @ sk_A @ sk_B)))
% 0.55/0.77        | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('sup-', [status(thm)], ['81', '95'])).
% 0.55/0.77  thf('97', plain,
% 0.55/0.77      ((((k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.77          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B))
% 0.55/0.77          = (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.77             (k11_yellow_6 @ sk_A @ sk_B)))
% 0.55/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.77        | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('simplify', [status(thm)], ['96'])).
% 0.55/0.77  thf('98', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('99', plain,
% 0.55/0.77      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.55/0.77      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.55/0.77  thf('100', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf(t18_waybel_9, axiom,
% 0.55/0.77    (![A:$i]:
% 0.55/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.55/0.77       ( ![B:$i]:
% 0.55/0.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.55/0.77           ( ![C:$i]:
% 0.55/0.77             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.77               ( ( k6_waybel_9 @ A @ A @ ( k4_waybel_1 @ A @ C ) @ B ) =
% 0.55/0.77                 ( k3_waybel_2 @ A @ C @ B ) ) ) ) ) ) ))).
% 0.55/0.77  thf('101', plain,
% 0.55/0.77      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.55/0.77         ((v2_struct_0 @ X24)
% 0.55/0.77          | ~ (l1_waybel_0 @ X24 @ X25)
% 0.55/0.77          | ((k6_waybel_9 @ X25 @ X25 @ (k4_waybel_1 @ X25 @ X26) @ X24)
% 0.55/0.77              = (k3_waybel_2 @ X25 @ X26 @ X24))
% 0.55/0.77          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 0.55/0.77          | ~ (l1_orders_2 @ X25)
% 0.55/0.77          | (v2_struct_0 @ X25))),
% 0.55/0.77      inference('cnf', [status(esa)], [t18_waybel_9])).
% 0.55/0.77  thf('102', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((v2_struct_0 @ sk_A)
% 0.55/0.77          | ~ (l1_orders_2 @ sk_A)
% 0.55/0.77          | ((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k3_waybel_2 @ sk_A @ sk_C @ X0))
% 0.55/0.77          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.55/0.77          | (v2_struct_0 @ X0))),
% 0.55/0.77      inference('sup-', [status(thm)], ['100', '101'])).
% 0.55/0.77  thf('103', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (l1_waybel_9 @ sk_A)
% 0.55/0.77          | (v2_struct_0 @ X0)
% 0.55/0.77          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.55/0.77          | ((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k3_waybel_2 @ sk_A @ sk_C @ X0))
% 0.55/0.77          | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('sup-', [status(thm)], ['99', '102'])).
% 0.55/0.77  thf('104', plain, ((l1_waybel_9 @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('105', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((v2_struct_0 @ X0)
% 0.55/0.77          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.55/0.77          | ((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)
% 0.55/0.77              = (k3_waybel_2 @ sk_A @ sk_C @ X0))
% 0.55/0.77          | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('demod', [status(thm)], ['103', '104'])).
% 0.55/0.77  thf('106', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A)
% 0.55/0.77        | ((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B)
% 0.55/0.77            = (k3_waybel_2 @ sk_A @ sk_C @ sk_B))
% 0.55/0.77        | (v2_struct_0 @ sk_B))),
% 0.55/0.77      inference('sup-', [status(thm)], ['98', '105'])).
% 0.55/0.77  thf('107', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('108', plain,
% 0.55/0.77      ((((k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B)
% 0.55/0.77          = (k3_waybel_2 @ sk_A @ sk_C @ sk_B))
% 0.55/0.77        | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('clc', [status(thm)], ['106', '107'])).
% 0.55/0.77  thf('109', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('110', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A) | (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C)))),
% 0.55/0.77      inference('demod', [status(thm)], ['35', '36'])).
% 0.55/0.77  thf('111', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A)
% 0.55/0.77        | (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77           (u1_struct_0 @ sk_A)))),
% 0.55/0.77      inference('demod', [status(thm)], ['42', '43'])).
% 0.55/0.77  thf('112', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A)
% 0.55/0.77        | (m1_subset_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.77           (k1_zfmisc_1 @ 
% 0.55/0.77            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 0.55/0.77      inference('demod', [status(thm)], ['49', '50'])).
% 0.55/0.77  thf(t25_waybel_9, axiom,
% 0.55/0.77    (![A:$i]:
% 0.55/0.77     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.55/0.77         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.55/0.77         ( v2_lattice3 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.55/0.77       ( ![B:$i]:
% 0.55/0.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.55/0.77             ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.55/0.77             ( l1_waybel_0 @ B @ A ) ) =>
% 0.55/0.77           ( ![C:$i]:
% 0.55/0.77             ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.77                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) & 
% 0.55/0.77                 ( m1_subset_1 @
% 0.55/0.77                   C @ 
% 0.55/0.77                   ( k1_zfmisc_1 @
% 0.55/0.77                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.55/0.77               ( ( v5_pre_topc @ C @ A @ A ) =>
% 0.55/0.77                 ( r2_hidden @
% 0.55/0.77                   ( k2_yellow_6 @
% 0.55/0.77                     ( u1_struct_0 @ A ) @ A @ C @ ( k11_yellow_6 @ A @ B ) ) @ 
% 0.55/0.77                   ( k10_yellow_6 @ A @ ( k6_waybel_9 @ A @ A @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.55/0.77  thf('113', plain,
% 0.55/0.77      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.55/0.77         ((v2_struct_0 @ X27)
% 0.55/0.77          | ~ (v4_orders_2 @ X27)
% 0.55/0.77          | ~ (v7_waybel_0 @ X27)
% 0.55/0.77          | ~ (v3_yellow_6 @ X27 @ X28)
% 0.55/0.77          | ~ (l1_waybel_0 @ X27 @ X28)
% 0.55/0.77          | ~ (v5_pre_topc @ X29 @ X28 @ X28)
% 0.55/0.77          | (r2_hidden @ 
% 0.55/0.77             (k2_yellow_6 @ (u1_struct_0 @ X28) @ X28 @ X29 @ 
% 0.55/0.77              (k11_yellow_6 @ X28 @ X27)) @ 
% 0.55/0.77             (k10_yellow_6 @ X28 @ (k6_waybel_9 @ X28 @ X28 @ X29 @ X27)))
% 0.55/0.77          | ~ (m1_subset_1 @ X29 @ 
% 0.55/0.77               (k1_zfmisc_1 @ 
% 0.55/0.77                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X28))))
% 0.55/0.77          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X28))
% 0.55/0.77          | ~ (v1_funct_1 @ X29)
% 0.55/0.77          | ~ (l1_waybel_9 @ X28)
% 0.55/0.77          | ~ (v2_lattice3 @ X28)
% 0.55/0.77          | ~ (v1_lattice3 @ X28)
% 0.55/0.77          | ~ (v5_orders_2 @ X28)
% 0.55/0.77          | ~ (v4_orders_2 @ X28)
% 0.55/0.77          | ~ (v3_orders_2 @ X28)
% 0.55/0.77          | ~ (v8_pre_topc @ X28)
% 0.55/0.77          | ~ (v2_pre_topc @ X28))),
% 0.55/0.77      inference('cnf', [status(esa)], [t25_waybel_9])).
% 0.55/0.77  thf('114', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((v2_struct_0 @ sk_A)
% 0.55/0.77          | ~ (v2_pre_topc @ sk_A)
% 0.55/0.77          | ~ (v8_pre_topc @ sk_A)
% 0.55/0.77          | ~ (v3_orders_2 @ sk_A)
% 0.55/0.77          | ~ (v4_orders_2 @ sk_A)
% 0.55/0.77          | ~ (v5_orders_2 @ sk_A)
% 0.55/0.77          | ~ (v1_lattice3 @ sk_A)
% 0.55/0.77          | ~ (v2_lattice3 @ sk_A)
% 0.55/0.77          | ~ (l1_waybel_9 @ sk_A)
% 0.55/0.77          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.55/0.77          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.77               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | (r2_hidden @ 
% 0.55/0.77             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.55/0.77             (k10_yellow_6 @ sk_A @ 
% 0.55/0.77              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.55/0.77          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_A @ sk_A)
% 0.55/0.77          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.55/0.77          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.55/0.77          | ~ (v7_waybel_0 @ X0)
% 0.55/0.77          | ~ (v4_orders_2 @ X0)
% 0.55/0.77          | (v2_struct_0 @ X0))),
% 0.55/0.77      inference('sup-', [status(thm)], ['112', '113'])).
% 0.55/0.77  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('116', plain, ((v8_pre_topc @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('117', plain, ((v3_orders_2 @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('118', plain, ((v4_orders_2 @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('119', plain, ((v5_orders_2 @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('120', plain, ((v1_lattice3 @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('121', plain, ((v2_lattice3 @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('122', plain, ((l1_waybel_9 @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('123', plain,
% 0.55/0.77      ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_A @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('124', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((v2_struct_0 @ sk_A)
% 0.55/0.77          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.55/0.77          | ~ (v1_funct_2 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.77               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.55/0.77          | (r2_hidden @ 
% 0.55/0.77             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.55/0.77             (k10_yellow_6 @ sk_A @ 
% 0.55/0.77              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.55/0.77          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.55/0.77          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.55/0.77          | ~ (v7_waybel_0 @ X0)
% 0.55/0.77          | ~ (v4_orders_2 @ X0)
% 0.55/0.77          | (v2_struct_0 @ X0))),
% 0.55/0.77      inference('demod', [status(thm)],
% 0.55/0.77                ['114', '115', '116', '117', '118', '119', '120', '121', 
% 0.55/0.77                 '122', '123'])).
% 0.55/0.77  thf('125', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((v2_struct_0 @ sk_A)
% 0.55/0.77          | (v2_struct_0 @ X0)
% 0.55/0.77          | ~ (v4_orders_2 @ X0)
% 0.55/0.77          | ~ (v7_waybel_0 @ X0)
% 0.55/0.77          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.55/0.77          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.55/0.77          | (r2_hidden @ 
% 0.55/0.77             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.55/0.77             (k10_yellow_6 @ sk_A @ 
% 0.55/0.77              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.55/0.77          | ~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.55/0.77          | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('sup-', [status(thm)], ['111', '124'])).
% 0.55/0.77  thf('126', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (v1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C))
% 0.55/0.77          | (r2_hidden @ 
% 0.55/0.77             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.55/0.77             (k10_yellow_6 @ sk_A @ 
% 0.55/0.77              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.55/0.77          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.55/0.77          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.55/0.77          | ~ (v7_waybel_0 @ X0)
% 0.55/0.77          | ~ (v4_orders_2 @ X0)
% 0.55/0.77          | (v2_struct_0 @ X0)
% 0.55/0.77          | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('simplify', [status(thm)], ['125'])).
% 0.55/0.77  thf('127', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((v2_struct_0 @ sk_A)
% 0.55/0.77          | (v2_struct_0 @ sk_A)
% 0.55/0.77          | (v2_struct_0 @ X0)
% 0.55/0.77          | ~ (v4_orders_2 @ X0)
% 0.55/0.77          | ~ (v7_waybel_0 @ X0)
% 0.55/0.77          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.55/0.77          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.55/0.77          | (r2_hidden @ 
% 0.55/0.77             (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.77              (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.55/0.77             (k10_yellow_6 @ sk_A @ 
% 0.55/0.77              (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['110', '126'])).
% 0.55/0.77  thf('128', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         ((r2_hidden @ 
% 0.55/0.77           (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.77            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ X0)) @ 
% 0.55/0.77           (k10_yellow_6 @ sk_A @ 
% 0.55/0.77            (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ X0)))
% 0.55/0.77          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.55/0.77          | ~ (v3_yellow_6 @ X0 @ sk_A)
% 0.55/0.77          | ~ (v7_waybel_0 @ X0)
% 0.55/0.77          | ~ (v4_orders_2 @ X0)
% 0.55/0.77          | (v2_struct_0 @ X0)
% 0.55/0.77          | (v2_struct_0 @ sk_A))),
% 0.55/0.77      inference('simplify', [status(thm)], ['127'])).
% 0.55/0.77  thf('129', plain,
% 0.55/0.77      (((v2_struct_0 @ sk_A)
% 0.55/0.77        | (v2_struct_0 @ sk_B)
% 0.55/0.77        | ~ (v4_orders_2 @ sk_B)
% 0.55/0.77        | ~ (v7_waybel_0 @ sk_B)
% 0.55/0.77        | ~ (v3_yellow_6 @ sk_B @ sk_A)
% 0.55/0.77        | (r2_hidden @ 
% 0.55/0.77           (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.77            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.55/0.77           (k10_yellow_6 @ sk_A @ 
% 0.55/0.77            (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B))))),
% 0.55/0.77      inference('sup-', [status(thm)], ['109', '128'])).
% 0.55/0.78  thf('130', plain, ((v4_orders_2 @ sk_B)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('131', plain, ((v7_waybel_0 @ sk_B)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('132', plain, ((v3_yellow_6 @ sk_B @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('133', plain,
% 0.55/0.78      (((v2_struct_0 @ sk_A)
% 0.55/0.78        | (v2_struct_0 @ sk_B)
% 0.55/0.78        | (r2_hidden @ 
% 0.55/0.78           (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.78            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.55/0.78           (k10_yellow_6 @ sk_A @ 
% 0.55/0.78            (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B))))),
% 0.55/0.78      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 0.55/0.78  thf('134', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('135', plain,
% 0.55/0.78      (((r2_hidden @ 
% 0.55/0.78         (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.78          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.55/0.78         (k10_yellow_6 @ sk_A @ 
% 0.55/0.78          (k6_waybel_9 @ sk_A @ sk_A @ (k4_waybel_1 @ sk_A @ sk_C) @ sk_B)))
% 0.55/0.78        | (v2_struct_0 @ sk_A))),
% 0.55/0.78      inference('clc', [status(thm)], ['133', '134'])).
% 0.55/0.78  thf('136', plain,
% 0.55/0.78      (((r2_hidden @ 
% 0.55/0.78         (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.78          (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.55/0.78         (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))
% 0.55/0.78        | (v2_struct_0 @ sk_A)
% 0.55/0.78        | (v2_struct_0 @ sk_A))),
% 0.55/0.78      inference('sup+', [status(thm)], ['108', '135'])).
% 0.55/0.78  thf('137', plain,
% 0.55/0.78      (((v2_struct_0 @ sk_A)
% 0.55/0.78        | (r2_hidden @ 
% 0.55/0.78           (k2_yellow_6 @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 0.55/0.78            (k4_waybel_1 @ sk_A @ sk_C) @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.55/0.78           (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B))))),
% 0.55/0.78      inference('simplify', [status(thm)], ['136'])).
% 0.55/0.78  thf('138', plain,
% 0.55/0.78      (((r2_hidden @ 
% 0.55/0.78         (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.78          (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.55/0.78         (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))
% 0.55/0.78        | (v2_struct_0 @ sk_A)
% 0.55/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.78        | (v2_struct_0 @ sk_A))),
% 0.55/0.78      inference('sup+', [status(thm)], ['97', '137'])).
% 0.55/0.78  thf('139', plain,
% 0.55/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.78        | (v2_struct_0 @ sk_A)
% 0.55/0.78        | (r2_hidden @ 
% 0.55/0.78           (k1_funct_1 @ (k4_waybel_1 @ sk_A @ sk_C) @ 
% 0.55/0.78            (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.55/0.78           (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B))))),
% 0.55/0.78      inference('simplify', [status(thm)], ['138'])).
% 0.55/0.78  thf('140', plain,
% 0.55/0.78      (((r2_hidden @ 
% 0.55/0.78         (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.55/0.78         (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))
% 0.55/0.78        | (v2_struct_0 @ sk_A)
% 0.55/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.78        | (v2_struct_0 @ sk_A)
% 0.55/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.78      inference('sup+', [status(thm)], ['80', '139'])).
% 0.55/0.78  thf('141', plain,
% 0.55/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.78        | (v2_struct_0 @ sk_A)
% 0.55/0.78        | (r2_hidden @ 
% 0.55/0.78           (k11_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.55/0.78           (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B))))),
% 0.55/0.78      inference('simplify', [status(thm)], ['140'])).
% 0.55/0.78  thf('142', plain,
% 0.55/0.78      (((r2_hidden @ 
% 0.55/0.78         (k12_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.55/0.78         (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))
% 0.55/0.78        | (v2_struct_0 @ sk_A)
% 0.55/0.78        | (v2_struct_0 @ sk_A)
% 0.55/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.78      inference('sup+', [status(thm)], ['28', '141'])).
% 0.55/0.78  thf('143', plain,
% 0.55/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.78        | (v2_struct_0 @ sk_A)
% 0.55/0.78        | (r2_hidden @ 
% 0.55/0.78           (k12_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.55/0.78           (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B))))),
% 0.55/0.78      inference('simplify', [status(thm)], ['142'])).
% 0.55/0.78  thf('144', plain,
% 0.55/0.78      (~ (r2_hidden @ 
% 0.55/0.78          (k12_lattice3 @ sk_A @ sk_C @ (k11_yellow_6 @ sk_A @ sk_B)) @ 
% 0.55/0.78          (k10_yellow_6 @ sk_A @ (k3_waybel_2 @ sk_A @ sk_C @ sk_B)))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('145', plain,
% 0.55/0.78      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.78      inference('clc', [status(thm)], ['143', '144'])).
% 0.55/0.78  thf('146', plain,
% 0.55/0.78      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.55/0.78        | ~ (l1_struct_0 @ sk_A)
% 0.55/0.78        | (v2_struct_0 @ sk_A))),
% 0.55/0.78      inference('sup+', [status(thm)], ['3', '145'])).
% 0.55/0.78  thf('147', plain, ((l1_waybel_9 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('148', plain,
% 0.55/0.78      (![X23 : $i]: ((l1_orders_2 @ X23) | ~ (l1_waybel_9 @ X23))),
% 0.55/0.78      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.55/0.78  thf(dt_l1_orders_2, axiom,
% 0.55/0.78    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.55/0.78  thf('149', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_orders_2 @ X5))),
% 0.55/0.78      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.55/0.78  thf('150', plain, (![X0 : $i]: (~ (l1_waybel_9 @ X0) | (l1_struct_0 @ X0))),
% 0.55/0.78      inference('sup-', [status(thm)], ['148', '149'])).
% 0.55/0.78  thf('151', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.78      inference('sup-', [status(thm)], ['147', '150'])).
% 0.55/0.78  thf('152', plain,
% 0.55/0.78      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.55/0.78      inference('demod', [status(thm)], ['146', '151'])).
% 0.55/0.78  thf(cc1_lattice3, axiom,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( l1_orders_2 @ A ) =>
% 0.55/0.78       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.55/0.78  thf('153', plain,
% 0.55/0.78      (![X6 : $i]:
% 0.55/0.78         (~ (v1_lattice3 @ X6) | ~ (v2_struct_0 @ X6) | ~ (l1_orders_2 @ X6))),
% 0.55/0.78      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.55/0.78  thf('154', plain,
% 0.55/0.78      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.55/0.78        | ~ (l1_orders_2 @ sk_A)
% 0.55/0.78        | ~ (v1_lattice3 @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['152', '153'])).
% 0.55/0.78  thf('155', plain, ((v1_lattice3 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('156', plain,
% 0.55/0.78      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | ~ (l1_orders_2 @ sk_A))),
% 0.55/0.78      inference('demod', [status(thm)], ['154', '155'])).
% 0.55/0.78  thf('157', plain,
% 0.55/0.78      ((~ (l1_waybel_9 @ sk_A) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['2', '156'])).
% 0.55/0.78  thf('158', plain, ((l1_waybel_9 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('159', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.55/0.78      inference('demod', [status(thm)], ['157', '158'])).
% 0.55/0.78  thf(fc2_yellow_0, axiom,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.55/0.78       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.55/0.78  thf('160', plain,
% 0.55/0.78      (![X12 : $i]:
% 0.55/0.78         (~ (v1_xboole_0 @ (k2_struct_0 @ X12))
% 0.55/0.78          | ~ (l1_orders_2 @ X12)
% 0.55/0.78          | (v2_struct_0 @ X12))),
% 0.55/0.78      inference('cnf', [status(esa)], [fc2_yellow_0])).
% 0.55/0.78  thf('161', plain, (((v2_struct_0 @ sk_A) | ~ (l1_orders_2 @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['159', '160'])).
% 0.55/0.78  thf('162', plain, ((~ (l1_waybel_9 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['1', '161'])).
% 0.55/0.78  thf('163', plain, ((l1_waybel_9 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('164', plain, ((v2_struct_0 @ sk_A)),
% 0.55/0.78      inference('demod', [status(thm)], ['162', '163'])).
% 0.55/0.78  thf('165', plain,
% 0.55/0.78      (![X6 : $i]:
% 0.55/0.78         (~ (v1_lattice3 @ X6) | ~ (v2_struct_0 @ X6) | ~ (l1_orders_2 @ X6))),
% 0.55/0.78      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.55/0.78  thf('166', plain, ((~ (l1_orders_2 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['164', '165'])).
% 0.55/0.78  thf('167', plain, ((v1_lattice3 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('168', plain, (~ (l1_orders_2 @ sk_A)),
% 0.55/0.78      inference('demod', [status(thm)], ['166', '167'])).
% 0.55/0.78  thf('169', plain, (~ (l1_waybel_9 @ sk_A)),
% 0.55/0.78      inference('sup-', [status(thm)], ['0', '168'])).
% 0.55/0.78  thf('170', plain, ((l1_waybel_9 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('171', plain, ($false), inference('demod', [status(thm)], ['169', '170'])).
% 0.55/0.78  
% 0.55/0.78  % SZS output end Refutation
% 0.55/0.78  
% 0.55/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
