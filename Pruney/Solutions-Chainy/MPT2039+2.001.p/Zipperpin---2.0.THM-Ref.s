%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IMrCPWE4lz

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:35 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  698 (55475 expanded)
%              Number of leaves         :   50 (16680 expanded)
%              Depth                    :  140
%              Number of atoms          : 12228 (1717083 expanded)
%              Number of equality atoms :   91 (4327 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(v10_waybel_0_type,type,(
    v10_waybel_0: $i > $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_waybel_9_type,type,(
    r1_waybel_9: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(k1_waybel_2_type,type,(
    k1_waybel_2: $i > $i > $i )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(dt_l1_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_waybel_9 @ A )
     => ( ( l1_pre_topc @ A )
        & ( l1_orders_2 @ A ) ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('1',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('2',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(t38_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v1_compts_1 @ A )
        & ( l1_waybel_9 @ A ) )
     => ( ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( v5_pre_topc @ ( k4_waybel_1 @ A @ B ) @ A @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ( ( v10_waybel_0 @ B @ A )
             => ( ( r1_waybel_9 @ A @ B )
                & ( r2_hidden @ ( k1_waybel_2 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( v8_pre_topc @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A )
          & ( v1_compts_1 @ A )
          & ( l1_waybel_9 @ A ) )
       => ( ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
             => ( v5_pre_topc @ ( k4_waybel_1 @ A @ B ) @ A @ A ) )
         => ! [B: $i] :
              ( ( ~ ( v2_struct_0 @ B )
                & ( v4_orders_2 @ B )
                & ( v7_waybel_0 @ B )
                & ( l1_waybel_0 @ B @ A ) )
             => ( ( v10_waybel_0 @ B @ A )
               => ( ( r1_waybel_9 @ A @ B )
                  & ( r2_hidden @ ( k1_waybel_2 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_waybel_9])).

thf('3',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( v1_compts_1 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ? [C: $i] :
              ( ( r3_waybel_9 @ A @ B @ C )
              & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( l1_waybel_0 @ X21 @ X22 )
      | ( r3_waybel_9 @ X22 @ X21 @ ( sk_C_1 @ X21 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v1_compts_1 @ X22 )
      | ~ ( v8_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t30_waybel_9])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v1_compts_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X11: $i] :
      ( ( l1_pre_topc @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['5','6','7','8','11','12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( l1_waybel_0 @ X21 @ X22 )
      | ( m1_subset_1 @ ( sk_C_1 @ X21 @ X22 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v1_compts_1 @ X22 )
      | ~ ( v8_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t30_waybel_9])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v1_compts_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('24',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21','22','23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('30',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(t35_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v1_compts_1 @ A )
        & ( l1_waybel_9 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v4_orders_2 @ C )
                & ( v7_waybel_0 @ C )
                & ( l1_waybel_0 @ C @ A ) )
             => ( ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( v5_pre_topc @ ( k4_waybel_1 @ A @ D ) @ A @ A ) )
                  & ( v10_waybel_0 @ C @ A )
                  & ( r3_waybel_9 @ A @ C @ B ) )
               => ( B
                  = ( k1_waybel_2 @ A @ C ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X27 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v10_waybel_0 @ X28 @ X27 )
      | ~ ( r3_waybel_9 @ X27 @ X28 @ X26 )
      | ( X26
        = ( k1_waybel_2 @ X27 @ X28 ) )
      | ~ ( l1_waybel_0 @ X28 @ X27 )
      | ~ ( v7_waybel_0 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_waybel_9 @ X27 )
      | ~ ( v1_compts_1 @ X27 )
      | ~ ( v2_lattice3 @ X27 )
      | ~ ( v1_lattice3 @ X27 )
      | ~ ( v5_orders_2 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ~ ( v3_orders_2 @ X27 )
      | ~ ( v8_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t35_waybel_9])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','35','36','37','38','39','40','41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v10_waybel_0 @ sk_B @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','42'])).

thf('44',plain,(
    v10_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X29: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X29 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_D_2 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X27 @ ( sk_D_2 @ X27 ) ) @ X27 @ X27 )
      | ~ ( v10_waybel_0 @ X28 @ X27 )
      | ~ ( r3_waybel_9 @ X27 @ X28 @ X26 )
      | ( X26
        = ( k1_waybel_2 @ X27 @ X28 ) )
      | ~ ( l1_waybel_0 @ X28 @ X27 )
      | ~ ( v7_waybel_0 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_waybel_9 @ X27 )
      | ~ ( v1_compts_1 @ X27 )
      | ~ ( v2_lattice3 @ X27 )
      | ~ ( v1_lattice3 @ X27 )
      | ~ ( v5_orders_2 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ~ ( v3_orders_2 @ X27 )
      | ~ ( v8_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t35_waybel_9])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( X1
        = ( k1_waybel_2 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( X1
        = ( k1_waybel_2 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57','58','59','60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_waybel_0 @ sk_B @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','65'])).

thf('67',plain,(
    v10_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('76',plain,
    ( ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('79',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('80',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('83',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('84',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('87',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('88',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(l48_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v1_compts_1 @ A )
        & ( l1_waybel_9 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ( C = D )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) )
                      & ( v10_waybel_0 @ B @ A )
                      & ( r3_waybel_9 @ A @ B @ C ) )
                   => ( r2_lattice3 @ A @ ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) ) @ D ) ) ) ) ) ) )).

thf('89',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v7_waybel_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( r2_lattice3 @ X13 @ ( k2_relset_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X13 ) @ ( u1_waybel_0 @ X13 @ X12 ) ) @ X14 )
      | ( X15 != X14 )
      | ~ ( r3_waybel_9 @ X13 @ X12 @ X15 )
      | ~ ( v10_waybel_0 @ X12 @ X13 )
      | ( m1_subset_1 @ ( sk_E @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_waybel_9 @ X13 )
      | ~ ( v1_compts_1 @ X13 )
      | ~ ( v2_lattice3 @ X13 )
      | ~ ( v1_lattice3 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ~ ( v8_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[l48_waybel_9])).

thf('90',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( v8_pre_topc @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v1_lattice3 @ X13 )
      | ~ ( v2_lattice3 @ X13 )
      | ~ ( v1_compts_1 @ X13 )
      | ~ ( l1_waybel_9 @ X13 )
      | ( m1_subset_1 @ ( sk_E @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v10_waybel_0 @ X12 @ X13 )
      | ~ ( r3_waybel_9 @ X13 @ X12 @ X14 )
      | ( r2_lattice3 @ X13 @ ( k2_relset_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X13 ) @ ( u1_waybel_0 @ X13 @ X12 ) ) @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( v7_waybel_0 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_waybel_9 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95','96','97','98','99','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v10_waybel_0 @ sk_B @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','101'])).

thf('103',plain,(
    v10_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['102','103','104','105','106'])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['86','108'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['107'])).

thf('113',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('114',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(t15_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( r1_yellow_0 @ A @ B )
        <=> ? [C: $i] :
              ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r2_lattice3 @ A @ B @ D )
                   => ( r1_orders_2 @ A @ C @ D ) ) )
              & ( r2_lattice3 @ A @ B @ C )
              & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('115',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X4 @ X5 @ X6 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( r2_lattice3 @ X6 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X6 ) )
      | ( r1_yellow_0 @ X6 @ X5 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v5_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf('120',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','121'])).

thf('123',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['111','123'])).

thf('125',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('128',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('129',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('132',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('135',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['107'])).

thf('138',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('139',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('140',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_lattice3 @ X6 @ X5 @ ( sk_D @ X4 @ X5 @ X6 ) )
      | ~ ( r2_lattice3 @ X6 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X6 ) )
      | ( r1_yellow_0 @ X6 @ X5 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v5_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['138','143'])).

thf('145',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['137','146'])).

thf('148',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['136','148'])).

thf('150',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf(l49_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( v1_compts_1 @ A )
        & ( l1_waybel_9 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ( C = D )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) )
                      & ( r3_waybel_9 @ A @ B @ C ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                       => ( ( r2_lattice3 @ A @ ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) ) @ E )
                         => ( r3_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) )).

thf('151',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_lattice3 @ X17 @ ( k2_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) @ ( u1_waybel_0 @ X17 @ X16 ) ) @ X19 )
      | ( r3_orders_2 @ X17 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( X20 != X18 )
      | ~ ( r3_waybel_9 @ X17 @ X16 @ X20 )
      | ( m1_subset_1 @ ( sk_E_1 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_waybel_9 @ X17 )
      | ~ ( v1_compts_1 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( v1_lattice3 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ~ ( v8_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[l49_waybel_9])).

thf('152',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( v8_pre_topc @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v1_lattice3 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( v1_compts_1 @ X17 )
      | ~ ( l1_waybel_9 @ X17 )
      | ( m1_subset_1 @ ( sk_E_1 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( r3_waybel_9 @ X17 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( r3_orders_2 @ X17 @ X18 @ X19 )
      | ~ ( r2_lattice3 @ X17 @ ( k2_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) @ ( u1_waybel_0 @ X17 @ X16 ) ) @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_waybel_9 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['150','152'])).

thf('154',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['153','154','155','156','157','158','159','160','161','162','163','164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['135','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','169'])).

thf('171',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['133','171'])).

thf('173',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('175',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('176',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( r3_orders_2 @ X1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['174','180'])).

thf('182',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['173','183'])).

thf('185',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','185'])).

thf('187',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_orders_2 @ X6 @ X4 @ ( sk_D @ X4 @ X5 @ X6 ) )
      | ~ ( r2_lattice3 @ X6 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X6 ) )
      | ( r1_yellow_0 @ X6 @ X5 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v5_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow_0])).

thf('189',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['131','192'])).

thf('194',plain,
    ( ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['130','194'])).

thf('196',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','196'])).

thf('198',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf(d3_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( ( r1_waybel_9 @ A @ B )
          <=> ( r1_yellow_0 @ A @ ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) ) ) ) ) ) )).

thf('200',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_waybel_0 @ X9 @ X10 )
      | ~ ( r1_yellow_0 @ X10 @ ( k2_relset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X10 ) @ ( u1_waybel_0 @ X10 @ X9 ) ) )
      | ( r1_waybel_9 @ X10 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_waybel_9])).

thf('201',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['128','203'])).

thf('205',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X29: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X29 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('210',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('211',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_lattice3 @ X17 @ ( k2_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) @ ( u1_waybel_0 @ X17 @ X16 ) ) @ X19 )
      | ( r3_orders_2 @ X17 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( X20 != X18 )
      | ~ ( r3_waybel_9 @ X17 @ X16 @ X20 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X17 @ ( sk_E_1 @ X17 ) ) @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_waybel_9 @ X17 )
      | ~ ( v1_compts_1 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( v1_lattice3 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ~ ( v8_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[l49_waybel_9])).

thf('212',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( v8_pre_topc @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v1_lattice3 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( v1_compts_1 @ X17 )
      | ~ ( l1_waybel_9 @ X17 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X17 @ ( sk_E_1 @ X17 ) ) @ X17 @ X17 )
      | ~ ( r3_waybel_9 @ X17 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( r3_orders_2 @ X17 @ X18 @ X19 )
      | ~ ( r2_lattice3 @ X17 @ ( k2_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) @ ( u1_waybel_0 @ X17 @ X16 ) ) @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( l1_waybel_9 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['210','212'])).

thf('214',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['213','214','215','216','217','218','219','220','221','222','223','224','225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['209','227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['208','229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['230'])).

thf('232',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['127','231'])).

thf('233',plain,
    ( ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','233'])).

thf('235',plain,
    ( ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('237',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','238'])).

thf('240',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['239'])).

thf('241',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_orders_2 @ X6 @ X4 @ ( sk_D @ X4 @ X5 @ X6 ) )
      | ~ ( r2_lattice3 @ X6 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X6 ) )
      | ( r1_yellow_0 @ X6 @ X5 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v5_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow_0])).

thf('242',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['242','243'])).

thf('245',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['244'])).

thf('246',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','245'])).

thf('247',plain,
    ( ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['246'])).

thf('248',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','247'])).

thf('249',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['248'])).

thf('250',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['84','249'])).

thf('251',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_waybel_0 @ X9 @ X10 )
      | ~ ( r1_yellow_0 @ X10 @ ( k2_relset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X10 ) @ ( u1_waybel_0 @ X10 @ X9 ) ) )
      | ( r1_waybel_9 @ X10 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_waybel_9])).

thf('254',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['254','255'])).

thf('257',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['256'])).

thf('258',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','257'])).

thf('259',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,(
    ! [X29: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X29 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v7_waybel_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( r2_lattice3 @ X13 @ ( k2_relset_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X13 ) @ ( u1_waybel_0 @ X13 @ X12 ) ) @ X14 )
      | ( X15 != X14 )
      | ~ ( r3_waybel_9 @ X13 @ X12 @ X15 )
      | ~ ( v10_waybel_0 @ X12 @ X13 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X13 @ ( sk_E @ X13 ) ) @ X13 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_waybel_9 @ X13 )
      | ~ ( v1_compts_1 @ X13 )
      | ~ ( v2_lattice3 @ X13 )
      | ~ ( v1_lattice3 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ~ ( v8_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[l48_waybel_9])).

thf('264',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( v8_pre_topc @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v1_lattice3 @ X13 )
      | ~ ( v2_lattice3 @ X13 )
      | ~ ( v1_compts_1 @ X13 )
      | ~ ( l1_waybel_9 @ X13 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X13 @ ( sk_E @ X13 ) ) @ X13 @ X13 )
      | ~ ( v10_waybel_0 @ X12 @ X13 )
      | ~ ( r3_waybel_9 @ X13 @ X12 @ X14 )
      | ( r2_lattice3 @ X13 @ ( k2_relset_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X13 ) @ ( u1_waybel_0 @ X13 @ X12 ) ) @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( v7_waybel_0 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(simplify,[status(thm)],['263'])).

thf('265',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ X1 )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ~ ( l1_waybel_9 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['262','264'])).

thf('266',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ X1 )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
      | ~ ( v10_waybel_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['265','266','267','268','269','270','271','272','273','274'])).

thf('276',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','275'])).

thf('277',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['276'])).

thf('278',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_waybel_0 @ sk_B @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['81','277'])).

thf('279',plain,(
    v10_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['278','279','280','281','282'])).

thf('284',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['283'])).

thf('285',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['283'])).

thf('286',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('287',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('288',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X4 @ X5 @ X6 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( r2_lattice3 @ X6 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X6 ) )
      | ( r1_yellow_0 @ X6 @ X5 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v5_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow_0])).

thf('289',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['287','288'])).

thf('290',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['289','290'])).

thf('292',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['286','291'])).

thf('293',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['292','293'])).

thf('295',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['285','294'])).

thf('296',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['295'])).

thf('297',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('298',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('299',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('300',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('301',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('302',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['283'])).

thf('303',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['295'])).

thf('304',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('305',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('306',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['295'])).

thf('307',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['283'])).

thf('308',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('309',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('310',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_lattice3 @ X6 @ X5 @ ( sk_D @ X4 @ X5 @ X6 ) )
      | ~ ( r2_lattice3 @ X6 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X6 ) )
      | ( r1_yellow_0 @ X6 @ X5 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v5_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow_0])).

thf('311',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['309','310'])).

thf('312',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['311','312'])).

thf('314',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['308','313'])).

thf('315',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( r1_yellow_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['314','315'])).

thf('317',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['307','316'])).

thf('318',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['317'])).

thf('319',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( v8_pre_topc @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v1_lattice3 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( v1_compts_1 @ X17 )
      | ~ ( l1_waybel_9 @ X17 )
      | ( m1_subset_1 @ ( sk_E_1 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( r3_waybel_9 @ X17 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( r3_orders_2 @ X17 @ X18 @ X19 )
      | ~ ( r2_lattice3 @ X17 @ ( k2_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) @ ( u1_waybel_0 @ X17 @ X16 ) ) @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('320',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_waybel_9 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['318','319'])).

thf('321',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('323',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('327',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('332',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['320','321','322','323','324','325','326','327','328','329','330','331','332'])).

thf('334',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['333'])).

thf('335',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['306','334'])).

thf('336',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['335'])).

thf('337',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['305','336'])).

thf('338',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['337'])).

thf('339',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['304','338'])).

thf('340',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['339'])).

thf('341',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('342',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['340','341'])).

thf('343',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['342'])).

thf('344',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['303','343'])).

thf('345',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['344'])).

thf('346',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_orders_2 @ X6 @ X4 @ ( sk_D @ X4 @ X5 @ X6 ) )
      | ~ ( r2_lattice3 @ X6 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X6 ) )
      | ( r1_yellow_0 @ X6 @ X5 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v5_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow_0])).

thf('347',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['345','346'])).

thf('348',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['347','348'])).

thf('350',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['349'])).

thf('351',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['302','350'])).

thf('352',plain,
    ( ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['351'])).

thf('353',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['301','352'])).

thf('354',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['353'])).

thf('355',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['300','354'])).

thf('356',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('357',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['355','356'])).

thf('358',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_waybel_0 @ X9 @ X10 )
      | ~ ( r1_yellow_0 @ X10 @ ( k2_relset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X10 ) @ ( u1_waybel_0 @ X10 @ X9 ) ) )
      | ( r1_waybel_9 @ X10 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_waybel_9])).

thf('359',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['357','358'])).

thf('360',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['359','360'])).

thf('362',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['361'])).

thf('363',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['299','362'])).

thf('364',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('365',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['363','364'])).

thf('366',plain,(
    ! [X29: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X29 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('367',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['365','366'])).

thf('368',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['295'])).

thf('369',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['317'])).

thf('370',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_pre_topc @ X17 )
      | ~ ( v8_pre_topc @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v1_lattice3 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( v1_compts_1 @ X17 )
      | ~ ( l1_waybel_9 @ X17 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X17 @ ( sk_E_1 @ X17 ) ) @ X17 @ X17 )
      | ~ ( r3_waybel_9 @ X17 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( r3_orders_2 @ X17 @ X18 @ X19 )
      | ~ ( r2_lattice3 @ X17 @ ( k2_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) @ ( u1_waybel_0 @ X17 @ X16 ) ) @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(simplify,[status(thm)],['211'])).

thf('371',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( l1_waybel_9 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['369','370'])).

thf('372',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('373',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('374',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('375',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('376',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('377',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('378',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('379',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('380',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('381',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('382',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('383',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('384',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['371','372','373','374','375','376','377','378','379','380','381','382','383'])).

thf('385',plain,(
    ! [X0: $i] :
      ( ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['384'])).

thf('386',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['368','385'])).

thf('387',plain,(
    ! [X0: $i] :
      ( ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['386'])).

thf('388',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['367','387'])).

thf('389',plain,(
    ! [X0: $i] :
      ( ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['388'])).

thf('390',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['298','389'])).

thf('391',plain,
    ( ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['390'])).

thf('392',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['297','391'])).

thf('393',plain,
    ( ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['392'])).

thf('394',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('395',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['393','394'])).

thf('396',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['395'])).

thf('397',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['296','396'])).

thf('398',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['397'])).

thf('399',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_orders_2 @ X6 @ X4 @ ( sk_D @ X4 @ X5 @ X6 ) )
      | ~ ( r2_lattice3 @ X6 @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X6 ) )
      | ( r1_yellow_0 @ X6 @ X5 )
      | ~ ( l1_orders_2 @ X6 )
      | ~ ( v5_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow_0])).

thf('400',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['398','399'])).

thf('401',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('402',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['400','401'])).

thf('403',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['402'])).

thf('404',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['284','403'])).

thf('405',plain,
    ( ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['404'])).

thf('406',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','405'])).

thf('407',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['406'])).

thf('408',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','407'])).

thf('409',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('410',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['408','409'])).

thf('411',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_waybel_0 @ X9 @ X10 )
      | ~ ( r1_yellow_0 @ X10 @ ( k2_relset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X10 ) @ ( u1_waybel_0 @ X10 @ X9 ) ) )
      | ( r1_waybel_9 @ X10 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_waybel_9])).

thf('412',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['410','411'])).

thf('413',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('414',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['412','413'])).

thf('415',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['414'])).

thf('416',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','415'])).

thf('417',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('418',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['416','417'])).

thf('419',plain,
    ( ~ ( r1_waybel_9 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('420',plain,
    ( ~ ( r1_waybel_9 @ sk_A @ sk_B )
   <= ~ ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['419'])).

thf('421',plain,(
    ! [X11: $i] :
      ( ( l1_orders_2 @ X11 )
      | ~ ( l1_waybel_9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('422',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('423',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('424',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(t33_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( v1_compts_1 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r3_waybel_9 @ A @ B @ C )
                        & ( r3_waybel_9 @ A @ B @ D ) )
                     => ( C = D ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r3_waybel_9 @ A @ B @ C )
                 => ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) )).

thf('425',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v7_waybel_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ~ ( r3_waybel_9 @ X24 @ X23 @ X25 )
      | ( r2_hidden @ X25 @ ( k10_yellow_6 @ X24 @ X23 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( r3_waybel_9 @ X24 @ X23 @ ( sk_C_2 @ X23 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v1_compts_1 @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('426',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_2 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['424','425'])).

thf('427',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('428',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('429',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('430',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('431',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_2 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['426','427','428','429','430'])).

thf('432',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_2 @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['431'])).

thf('433',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['423','432'])).

thf('434',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('435',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('436',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('437',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['433','434','435','436'])).

thf('438',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['437'])).

thf('439',plain,
    ( ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['422','438'])).

thf('440',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['439'])).

thf('441',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['419'])).

thf('442',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['440','441'])).

thf('443',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('444',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['442','443'])).

thf('445',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('446',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('447',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('448',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v7_waybel_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ~ ( r3_waybel_9 @ X24 @ X23 @ X25 )
      | ( r2_hidden @ X25 @ ( k10_yellow_6 @ X24 @ X23 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( m1_subset_1 @ ( sk_C_2 @ X23 @ X24 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v1_compts_1 @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('449',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( sk_C_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['447','448'])).

thf('450',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('451',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('452',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('453',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('454',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['449','450','451','452','453'])).

thf('455',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_C_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['454'])).

thf('456',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['446','455'])).

thf('457',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('458',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('459',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('460',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['456','457','458','459'])).

thf('461',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['460'])).

thf('462',plain,
    ( ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['445','461'])).

thf('463',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['462'])).

thf('464',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['419'])).

thf('465',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['463','464'])).

thf('466',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('467',plain,
    ( ( ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['465','466'])).

thf('468',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['442','443'])).

thf('469',plain,
    ( ( ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['465','466'])).

thf('470',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X27 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v10_waybel_0 @ X28 @ X27 )
      | ~ ( r3_waybel_9 @ X27 @ X28 @ X26 )
      | ( X26
        = ( k1_waybel_2 @ X27 @ X28 ) )
      | ~ ( l1_waybel_0 @ X28 @ X27 )
      | ~ ( v7_waybel_0 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_waybel_9 @ X27 )
      | ~ ( v1_compts_1 @ X27 )
      | ~ ( v2_lattice3 @ X27 )
      | ~ ( v1_lattice3 @ X27 )
      | ~ ( v5_orders_2 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ~ ( v3_orders_2 @ X27 )
      | ~ ( v8_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t35_waybel_9])).

thf('471',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( v8_pre_topc @ sk_A )
        | ~ ( v3_orders_2 @ sk_A )
        | ~ ( v4_orders_2 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_lattice3 @ sk_A )
        | ~ ( v2_lattice3 @ sk_A )
        | ~ ( v1_compts_1 @ sk_A )
        | ~ ( l1_waybel_9 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( ( sk_C_2 @ sk_B @ sk_A )
          = ( k1_waybel_2 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_2 @ sk_B @ sk_A ) )
        | ~ ( v10_waybel_0 @ X0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['469','470'])).

thf('472',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('473',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('474',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('475',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('476',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('477',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('478',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('479',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('480',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('481',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( ( sk_C_2 @ sk_B @ sk_A )
          = ( k1_waybel_2 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_2 @ sk_B @ sk_A ) )
        | ~ ( v10_waybel_0 @ X0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['471','472','473','474','475','476','477','478','479','480'])).

thf('482',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v10_waybel_0 @ sk_B @ sk_A )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['468','481'])).

thf('483',plain,(
    v10_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('484',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('485',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('486',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('487',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['482','483','484','485','486'])).

thf('488',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['487'])).

thf('489',plain,(
    ! [X29: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X29 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('490',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_D_2 @ sk_A ) ) @ sk_A @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['488','489'])).

thf('491',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X27 @ ( sk_D_2 @ X27 ) ) @ X27 @ X27 )
      | ~ ( v10_waybel_0 @ X28 @ X27 )
      | ~ ( r3_waybel_9 @ X27 @ X28 @ X26 )
      | ( X26
        = ( k1_waybel_2 @ X27 @ X28 ) )
      | ~ ( l1_waybel_0 @ X28 @ X27 )
      | ~ ( v7_waybel_0 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_waybel_9 @ X27 )
      | ~ ( v1_compts_1 @ X27 )
      | ~ ( v2_lattice3 @ X27 )
      | ~ ( v1_lattice3 @ X27 )
      | ~ ( v5_orders_2 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ~ ( v3_orders_2 @ X27 )
      | ~ ( v8_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t35_waybel_9])).

thf('492',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( ( sk_C_2 @ sk_B @ sk_A )
          = ( k1_waybel_2 @ sk_A @ sk_B ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( v8_pre_topc @ sk_A )
        | ~ ( v3_orders_2 @ sk_A )
        | ~ ( v4_orders_2 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_lattice3 @ sk_A )
        | ~ ( v2_lattice3 @ sk_A )
        | ~ ( v1_compts_1 @ sk_A )
        | ~ ( l1_waybel_9 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( X1
          = ( k1_waybel_2 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
        | ~ ( v10_waybel_0 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['490','491'])).

thf('493',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('494',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('495',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('496',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('497',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('498',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('499',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('500',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('501',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('502',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( ( sk_C_2 @ sk_B @ sk_A )
          = ( k1_waybel_2 @ sk_A @ sk_B ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( X1
          = ( k1_waybel_2 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
        | ~ ( v10_waybel_0 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['492','493','494','495','496','497','498','499','500','501'])).

thf('503',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v10_waybel_0 @ X0 @ sk_A )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_2 @ sk_B @ sk_A ) )
        | ( ( sk_C_2 @ sk_B @ sk_A )
          = ( k1_waybel_2 @ sk_A @ X0 ) )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_C_2 @ sk_B @ sk_A )
          = ( k1_waybel_2 @ sk_A @ sk_B ) )
        | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['467','502'])).

thf('504',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( ( sk_C_2 @ sk_B @ sk_A )
          = ( k1_waybel_2 @ sk_A @ sk_B ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( ( sk_C_2 @ sk_B @ sk_A )
          = ( k1_waybel_2 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_2 @ sk_B @ sk_A ) )
        | ~ ( v10_waybel_0 @ X0 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['503'])).

thf('505',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_waybel_0 @ sk_B @ sk_A )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['444','504'])).

thf('506',plain,(
    v10_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('507',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('508',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('509',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('510',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['505','506','507','508','509'])).

thf('511',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['510'])).

thf('512',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('513',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['511','512'])).

thf('514',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('515',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('516',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v7_waybel_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ~ ( r3_waybel_9 @ X24 @ X23 @ X25 )
      | ( r2_hidden @ X25 @ ( k10_yellow_6 @ X24 @ X23 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( r3_waybel_9 @ X24 @ X23 @ ( sk_D_1 @ X23 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v1_compts_1 @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('517',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['515','516'])).

thf('518',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('519',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('520',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('521',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('522',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['517','518','519','520','521'])).

thf('523',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['522'])).

thf('524',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['514','523'])).

thf('525',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('526',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('527',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('528',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['524','525','526','527'])).

thf('529',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['528'])).

thf('530',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['419'])).

thf('531',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['529','530'])).

thf('532',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('533',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['531','532'])).

thf('534',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('535',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('536',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('537',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v7_waybel_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ~ ( r3_waybel_9 @ X24 @ X23 @ X25 )
      | ( r2_hidden @ X25 @ ( k10_yellow_6 @ X24 @ X23 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X23 @ X24 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v1_compts_1 @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('538',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['536','537'])).

thf('539',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('540',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('541',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('542',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('543',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['538','539','540','541','542'])).

thf('544',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['543'])).

thf('545',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['535','544'])).

thf('546',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('547',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('548',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('549',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['545','546','547','548'])).

thf('550',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['549'])).

thf('551',plain,
    ( ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['534','550'])).

thf('552',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['551'])).

thf('553',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['419'])).

thf('554',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['552','553'])).

thf('555',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('556',plain,
    ( ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['554','555'])).

thf('557',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['531','532'])).

thf('558',plain,
    ( ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['554','555'])).

thf('559',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X27 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v10_waybel_0 @ X28 @ X27 )
      | ~ ( r3_waybel_9 @ X27 @ X28 @ X26 )
      | ( X26
        = ( k1_waybel_2 @ X27 @ X28 ) )
      | ~ ( l1_waybel_0 @ X28 @ X27 )
      | ~ ( v7_waybel_0 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_waybel_9 @ X27 )
      | ~ ( v1_compts_1 @ X27 )
      | ~ ( v2_lattice3 @ X27 )
      | ~ ( v1_lattice3 @ X27 )
      | ~ ( v5_orders_2 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ~ ( v3_orders_2 @ X27 )
      | ~ ( v8_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t35_waybel_9])).

thf('560',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( v8_pre_topc @ sk_A )
        | ~ ( v3_orders_2 @ sk_A )
        | ~ ( v4_orders_2 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_lattice3 @ sk_A )
        | ~ ( v2_lattice3 @ sk_A )
        | ~ ( v1_compts_1 @ sk_A )
        | ~ ( l1_waybel_9 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( ( sk_D_1 @ sk_B @ sk_A )
          = ( k1_waybel_2 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ sk_A ) )
        | ~ ( v10_waybel_0 @ X0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['558','559'])).

thf('561',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('562',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('563',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('564',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('565',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('566',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('567',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('568',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('569',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('570',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( ( sk_D_1 @ sk_B @ sk_A )
          = ( k1_waybel_2 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ sk_A ) )
        | ~ ( v10_waybel_0 @ X0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['560','561','562','563','564','565','566','567','568','569'])).

thf('571',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v10_waybel_0 @ sk_B @ sk_A )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['557','570'])).

thf('572',plain,(
    v10_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('573',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('574',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('575',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('576',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['571','572','573','574','575'])).

thf('577',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['576'])).

thf('578',plain,(
    ! [X29: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X29 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('579',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_D_2 @ sk_A ) ) @ sk_A @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['577','578'])).

thf('580',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X27 @ ( sk_D_2 @ X27 ) ) @ X27 @ X27 )
      | ~ ( v10_waybel_0 @ X28 @ X27 )
      | ~ ( r3_waybel_9 @ X27 @ X28 @ X26 )
      | ( X26
        = ( k1_waybel_2 @ X27 @ X28 ) )
      | ~ ( l1_waybel_0 @ X28 @ X27 )
      | ~ ( v7_waybel_0 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_waybel_9 @ X27 )
      | ~ ( v1_compts_1 @ X27 )
      | ~ ( v2_lattice3 @ X27 )
      | ~ ( v1_lattice3 @ X27 )
      | ~ ( v5_orders_2 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ~ ( v3_orders_2 @ X27 )
      | ~ ( v8_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t35_waybel_9])).

thf('581',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( ( sk_D_1 @ sk_B @ sk_A )
          = ( k1_waybel_2 @ sk_A @ sk_B ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( v8_pre_topc @ sk_A )
        | ~ ( v3_orders_2 @ sk_A )
        | ~ ( v4_orders_2 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_lattice3 @ sk_A )
        | ~ ( v2_lattice3 @ sk_A )
        | ~ ( v1_compts_1 @ sk_A )
        | ~ ( l1_waybel_9 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( X1
          = ( k1_waybel_2 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
        | ~ ( v10_waybel_0 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['579','580'])).

thf('582',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('583',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('584',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('585',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('586',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('587',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('588',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('589',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('590',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('591',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( ( sk_D_1 @ sk_B @ sk_A )
          = ( k1_waybel_2 @ sk_A @ sk_B ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( X1
          = ( k1_waybel_2 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
        | ~ ( v10_waybel_0 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['581','582','583','584','585','586','587','588','589','590'])).

thf('592',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v10_waybel_0 @ X0 @ sk_A )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ sk_A ) )
        | ( ( sk_D_1 @ sk_B @ sk_A )
          = ( k1_waybel_2 @ sk_A @ X0 ) )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_1 @ sk_B @ sk_A )
          = ( k1_waybel_2 @ sk_A @ sk_B ) )
        | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['556','591'])).

thf('593',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( ( sk_D_1 @ sk_B @ sk_A )
          = ( k1_waybel_2 @ sk_A @ sk_B ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( ( sk_D_1 @ sk_B @ sk_A )
          = ( k1_waybel_2 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ sk_A ) )
        | ~ ( v10_waybel_0 @ X0 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['592'])).

thf('594',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_waybel_0 @ sk_B @ sk_A )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['533','593'])).

thf('595',plain,(
    v10_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('596',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('597',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('598',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('599',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['594','595','596','597','598'])).

thf('600',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['599'])).

thf('601',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('602',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['600','601'])).

thf('603',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('604',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('605',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v7_waybel_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ~ ( r3_waybel_9 @ X24 @ X23 @ X25 )
      | ( r2_hidden @ X25 @ ( k10_yellow_6 @ X24 @ X23 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( ( sk_C_2 @ X23 @ X24 )
       != ( sk_D_1 @ X23 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v1_compts_1 @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('606',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( ( sk_C_2 @ X0 @ sk_A )
       != ( sk_D_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['604','605'])).

thf('607',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('608',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('609',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('610',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('611',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C_2 @ X0 @ sk_A )
       != ( sk_D_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['606','607','608','609','610'])).

thf('612',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( ( sk_C_2 @ X0 @ sk_A )
       != ( sk_D_1 @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['611'])).

thf('613',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_C_2 @ sk_B @ sk_A )
     != ( sk_D_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['603','612'])).

thf('614',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('615',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('616',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('617',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_C_2 @ sk_B @ sk_A )
     != ( sk_D_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['613','614','615','616'])).

thf('618',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( ( sk_C_2 @ sk_B @ sk_A )
     != ( sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['617'])).

thf('619',plain,
    ( ( ( ( sk_C_2 @ sk_B @ sk_A )
       != ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['602','618'])).

thf('620',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C_2 @ sk_B @ sk_A )
       != ( k1_waybel_2 @ sk_A @ sk_B ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['619'])).

thf('621',plain,
    ( ( ( ( k1_waybel_2 @ sk_A @ sk_B )
       != ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['513','620'])).

thf('622',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['621'])).

thf('623',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('624',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['622','623'])).

thf('625',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['419'])).

thf('626',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['624','625'])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('627',plain,(
    ! [X3: $i] :
      ( ~ ( v1_lattice3 @ X3 )
      | ~ ( v2_struct_0 @ X3 )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('628',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['626','627'])).

thf('629',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('630',plain,
    ( ~ ( l1_orders_2 @ sk_A )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['628','629'])).

thf('631',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['421','630'])).

thf('632',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('633',plain,(
    r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['631','632'])).

thf('634',plain,
    ( ~ ( r1_waybel_9 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['419'])).

thf('635',plain,(
    ~ ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['633','634'])).

thf('636',plain,(
    ~ ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['420','635'])).

thf('637',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['418','636'])).

thf('638',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('639',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['637','638'])).

thf('640',plain,(
    ! [X3: $i] :
      ( ~ ( v1_lattice3 @ X3 )
      | ~ ( v2_struct_0 @ X3 )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('641',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['639','640'])).

thf('642',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('643',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['641','642'])).

thf('644',plain,(
    ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','643'])).

thf('645',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('646',plain,(
    $false ),
    inference(demod,[status(thm)],['644','645'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IMrCPWE4lz
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.82/1.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.82/1.06  % Solved by: fo/fo7.sh
% 0.82/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.06  % done 911 iterations in 0.584s
% 0.82/1.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.82/1.06  % SZS output start Refutation
% 0.82/1.06  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.82/1.06  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.82/1.06  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.82/1.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.82/1.06  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.82/1.06  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 0.82/1.06  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 0.82/1.06  thf(v10_waybel_0_type, type, v10_waybel_0: $i > $i > $o).
% 0.82/1.06  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.82/1.06  thf(sk_D_2_type, type, sk_D_2: $i > $i).
% 0.82/1.06  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.82/1.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.82/1.06  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.82/1.06  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 0.82/1.06  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.82/1.06  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.82/1.06  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.82/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.06  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.82/1.06  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.82/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.06  thf(r1_waybel_9_type, type, r1_waybel_9: $i > $i > $o).
% 0.82/1.06  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.82/1.06  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.82/1.06  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.82/1.06  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.82/1.06  thf(sk_E_type, type, sk_E: $i > $i).
% 0.82/1.06  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 0.82/1.06  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.82/1.06  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.82/1.06  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.82/1.06  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 0.82/1.06  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.82/1.06  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.82/1.06  thf(k1_waybel_2_type, type, k1_waybel_2: $i > $i > $i).
% 0.82/1.06  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.82/1.06  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.82/1.06  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.82/1.06  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.82/1.06  thf(dt_l1_waybel_9, axiom,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 0.82/1.06  thf('0', plain, (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.82/1.06      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.82/1.06  thf('1', plain, (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.82/1.06      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.82/1.06  thf('2', plain, (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.82/1.06      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.82/1.06  thf(t38_waybel_9, conjecture,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.82/1.06         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.82/1.06         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.82/1.06       ( ( ![B:$i]:
% 0.82/1.06           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.06             ( v5_pre_topc @ ( k4_waybel_1 @ A @ B ) @ A @ A ) ) ) =>
% 0.82/1.06         ( ![B:$i]:
% 0.82/1.06           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.82/1.06               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.82/1.06             ( ( v10_waybel_0 @ B @ A ) =>
% 0.82/1.06               ( ( r1_waybel_9 @ A @ B ) & 
% 0.82/1.06                 ( r2_hidden @
% 0.82/1.06                   ( k1_waybel_2 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ))).
% 0.82/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.06    (~( ![A:$i]:
% 0.82/1.06        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.82/1.06            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.82/1.06            ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.82/1.06          ( ( ![B:$i]:
% 0.82/1.06              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.06                ( v5_pre_topc @ ( k4_waybel_1 @ A @ B ) @ A @ A ) ) ) =>
% 0.82/1.06            ( ![B:$i]:
% 0.82/1.06              ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.82/1.06                  ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.82/1.06                ( ( v10_waybel_0 @ B @ A ) =>
% 0.82/1.06                  ( ( r1_waybel_9 @ A @ B ) & 
% 0.82/1.06                    ( r2_hidden @
% 0.82/1.06                      ( k1_waybel_2 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ) )),
% 0.82/1.06    inference('cnf.neg', [status(esa)], [t38_waybel_9])).
% 0.82/1.06  thf('3', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf(t30_waybel_9, axiom,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.82/1.06         ( v8_pre_topc @ A ) & ( v1_compts_1 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.82/1.06       ( ![B:$i]:
% 0.82/1.06         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.82/1.06             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.82/1.06           ( ?[C:$i]:
% 0.82/1.06             ( ( r3_waybel_9 @ A @ B @ C ) & 
% 0.82/1.06               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.82/1.06  thf('4', plain,
% 0.82/1.06      (![X21 : $i, X22 : $i]:
% 0.82/1.06         ((v2_struct_0 @ X21)
% 0.82/1.06          | ~ (v4_orders_2 @ X21)
% 0.82/1.06          | ~ (v7_waybel_0 @ X21)
% 0.82/1.06          | ~ (l1_waybel_0 @ X21 @ X22)
% 0.82/1.06          | (r3_waybel_9 @ X22 @ X21 @ (sk_C_1 @ X21 @ X22))
% 0.82/1.06          | ~ (l1_pre_topc @ X22)
% 0.82/1.06          | ~ (v1_compts_1 @ X22)
% 0.82/1.06          | ~ (v8_pre_topc @ X22)
% 0.82/1.06          | ~ (v2_pre_topc @ X22)
% 0.82/1.06          | (v2_struct_0 @ X22))),
% 0.82/1.06      inference('cnf', [status(esa)], [t30_waybel_9])).
% 0.82/1.06  thf('5', plain,
% 0.82/1.06      (((v2_struct_0 @ sk_A)
% 0.82/1.06        | ~ (v2_pre_topc @ sk_A)
% 0.82/1.06        | ~ (v8_pre_topc @ sk_A)
% 0.82/1.06        | ~ (v1_compts_1 @ sk_A)
% 0.82/1.06        | ~ (l1_pre_topc @ sk_A)
% 0.82/1.06        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.82/1.06        | ~ (v7_waybel_0 @ sk_B)
% 0.82/1.06        | ~ (v4_orders_2 @ sk_B)
% 0.82/1.06        | (v2_struct_0 @ sk_B))),
% 0.82/1.06      inference('sup-', [status(thm)], ['3', '4'])).
% 0.82/1.06  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('7', plain, ((v8_pre_topc @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('8', plain, ((v1_compts_1 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('9', plain, ((l1_waybel_9 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('10', plain,
% 0.82/1.06      (![X11 : $i]: ((l1_pre_topc @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.82/1.06      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.82/1.06  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.06      inference('sup-', [status(thm)], ['9', '10'])).
% 0.82/1.06  thf('12', plain, ((v7_waybel_0 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('13', plain, ((v4_orders_2 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('14', plain,
% 0.82/1.06      (((v2_struct_0 @ sk_A)
% 0.82/1.06        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.82/1.06        | (v2_struct_0 @ sk_B))),
% 0.82/1.06      inference('demod', [status(thm)], ['5', '6', '7', '8', '11', '12', '13'])).
% 0.82/1.06  thf('15', plain, (~ (v2_struct_0 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('16', plain,
% 0.82/1.06      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.82/1.06        | (v2_struct_0 @ sk_A))),
% 0.82/1.06      inference('clc', [status(thm)], ['14', '15'])).
% 0.82/1.06  thf('17', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('18', plain,
% 0.82/1.06      (![X21 : $i, X22 : $i]:
% 0.82/1.06         ((v2_struct_0 @ X21)
% 0.82/1.06          | ~ (v4_orders_2 @ X21)
% 0.82/1.06          | ~ (v7_waybel_0 @ X21)
% 0.82/1.06          | ~ (l1_waybel_0 @ X21 @ X22)
% 0.82/1.06          | (m1_subset_1 @ (sk_C_1 @ X21 @ X22) @ (u1_struct_0 @ X22))
% 0.82/1.06          | ~ (l1_pre_topc @ X22)
% 0.82/1.06          | ~ (v1_compts_1 @ X22)
% 0.82/1.06          | ~ (v8_pre_topc @ X22)
% 0.82/1.06          | ~ (v2_pre_topc @ X22)
% 0.82/1.06          | (v2_struct_0 @ X22))),
% 0.82/1.06      inference('cnf', [status(esa)], [t30_waybel_9])).
% 0.82/1.06  thf('19', plain,
% 0.82/1.06      (((v2_struct_0 @ sk_A)
% 0.82/1.06        | ~ (v2_pre_topc @ sk_A)
% 0.82/1.06        | ~ (v8_pre_topc @ sk_A)
% 0.82/1.06        | ~ (v1_compts_1 @ sk_A)
% 0.82/1.06        | ~ (l1_pre_topc @ sk_A)
% 0.82/1.06        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.06        | ~ (v7_waybel_0 @ sk_B)
% 0.82/1.06        | ~ (v4_orders_2 @ sk_B)
% 0.82/1.06        | (v2_struct_0 @ sk_B))),
% 0.82/1.06      inference('sup-', [status(thm)], ['17', '18'])).
% 0.82/1.06  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('21', plain, ((v8_pre_topc @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('22', plain, ((v1_compts_1 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.82/1.06      inference('sup-', [status(thm)], ['9', '10'])).
% 0.82/1.06  thf('24', plain, ((v7_waybel_0 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('25', plain, ((v4_orders_2 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('26', plain,
% 0.82/1.06      (((v2_struct_0 @ sk_A)
% 0.82/1.06        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.06        | (v2_struct_0 @ sk_B))),
% 0.82/1.06      inference('demod', [status(thm)],
% 0.82/1.06                ['19', '20', '21', '22', '23', '24', '25'])).
% 0.82/1.06  thf('27', plain, (~ (v2_struct_0 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('28', plain,
% 0.82/1.06      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.06        | (v2_struct_0 @ sk_A))),
% 0.82/1.06      inference('clc', [status(thm)], ['26', '27'])).
% 0.82/1.06  thf('29', plain,
% 0.82/1.06      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.82/1.06        | (v2_struct_0 @ sk_A))),
% 0.82/1.06      inference('clc', [status(thm)], ['14', '15'])).
% 0.82/1.06  thf('30', plain,
% 0.82/1.06      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.06        | (v2_struct_0 @ sk_A))),
% 0.82/1.06      inference('clc', [status(thm)], ['26', '27'])).
% 0.82/1.06  thf(t35_waybel_9, axiom,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.82/1.06         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.82/1.06         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.82/1.06       ( ![B:$i]:
% 0.82/1.06         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.06           ( ![C:$i]:
% 0.82/1.06             ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 0.82/1.06                 ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 0.82/1.06               ( ( ( ![D:$i]:
% 0.82/1.06                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.06                       ( v5_pre_topc @ ( k4_waybel_1 @ A @ D ) @ A @ A ) ) ) & 
% 0.82/1.06                   ( v10_waybel_0 @ C @ A ) & ( r3_waybel_9 @ A @ C @ B ) ) =>
% 0.82/1.06                 ( ( B ) = ( k1_waybel_2 @ A @ C ) ) ) ) ) ) ) ))).
% 0.82/1.06  thf('31', plain,
% 0.82/1.06      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.82/1.06         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.82/1.06          | (m1_subset_1 @ (sk_D_2 @ X27) @ (u1_struct_0 @ X27))
% 0.82/1.06          | ~ (v10_waybel_0 @ X28 @ X27)
% 0.82/1.06          | ~ (r3_waybel_9 @ X27 @ X28 @ X26)
% 0.82/1.06          | ((X26) = (k1_waybel_2 @ X27 @ X28))
% 0.82/1.06          | ~ (l1_waybel_0 @ X28 @ X27)
% 0.82/1.06          | ~ (v7_waybel_0 @ X28)
% 0.82/1.06          | ~ (v4_orders_2 @ X28)
% 0.82/1.06          | (v2_struct_0 @ X28)
% 0.82/1.06          | ~ (l1_waybel_9 @ X27)
% 0.82/1.06          | ~ (v1_compts_1 @ X27)
% 0.82/1.06          | ~ (v2_lattice3 @ X27)
% 0.82/1.06          | ~ (v1_lattice3 @ X27)
% 0.82/1.06          | ~ (v5_orders_2 @ X27)
% 0.82/1.06          | ~ (v4_orders_2 @ X27)
% 0.82/1.06          | ~ (v3_orders_2 @ X27)
% 0.82/1.06          | ~ (v8_pre_topc @ X27)
% 0.82/1.06          | ~ (v2_pre_topc @ X27))),
% 0.82/1.06      inference('cnf', [status(esa)], [t35_waybel_9])).
% 0.82/1.06  thf('32', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         ((v2_struct_0 @ sk_A)
% 0.82/1.06          | ~ (v2_pre_topc @ sk_A)
% 0.82/1.06          | ~ (v8_pre_topc @ sk_A)
% 0.82/1.06          | ~ (v3_orders_2 @ sk_A)
% 0.82/1.06          | ~ (v4_orders_2 @ sk_A)
% 0.82/1.06          | ~ (v5_orders_2 @ sk_A)
% 0.82/1.06          | ~ (v1_lattice3 @ sk_A)
% 0.82/1.06          | ~ (v2_lattice3 @ sk_A)
% 0.82/1.06          | ~ (v1_compts_1 @ sk_A)
% 0.82/1.06          | ~ (l1_waybel_9 @ sk_A)
% 0.82/1.06          | (v2_struct_0 @ X0)
% 0.82/1.06          | ~ (v4_orders_2 @ X0)
% 0.82/1.06          | ~ (v7_waybel_0 @ X0)
% 0.82/1.06          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.82/1.06          | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 0.82/1.06          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.82/1.06          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.82/1.06          | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.06      inference('sup-', [status(thm)], ['30', '31'])).
% 0.82/1.06  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('34', plain, ((v8_pre_topc @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('35', plain, ((v3_orders_2 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('36', plain, ((v4_orders_2 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('37', plain, ((v5_orders_2 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('38', plain, ((v1_lattice3 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('39', plain, ((v2_lattice3 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('40', plain, ((v1_compts_1 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('41', plain, ((l1_waybel_9 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('42', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         ((v2_struct_0 @ sk_A)
% 0.82/1.06          | (v2_struct_0 @ X0)
% 0.82/1.06          | ~ (v4_orders_2 @ X0)
% 0.82/1.06          | ~ (v7_waybel_0 @ X0)
% 0.82/1.06          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.82/1.06          | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 0.82/1.06          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.82/1.06          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.82/1.06          | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.06      inference('demod', [status(thm)],
% 0.82/1.06                ['32', '33', '34', '35', '36', '37', '38', '39', '40', '41'])).
% 0.82/1.06  thf('43', plain,
% 0.82/1.06      (((v2_struct_0 @ sk_A)
% 0.82/1.06        | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.06        | ~ (v10_waybel_0 @ sk_B @ sk_A)
% 0.82/1.06        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.82/1.06        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.82/1.06        | ~ (v7_waybel_0 @ sk_B)
% 0.82/1.06        | ~ (v4_orders_2 @ sk_B)
% 0.82/1.06        | (v2_struct_0 @ sk_B)
% 0.82/1.06        | (v2_struct_0 @ sk_A))),
% 0.82/1.06      inference('sup-', [status(thm)], ['29', '42'])).
% 0.82/1.06  thf('44', plain, ((v10_waybel_0 @ sk_B @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('45', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('46', plain, ((v7_waybel_0 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('47', plain, ((v4_orders_2 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('48', plain,
% 0.82/1.06      (((v2_struct_0 @ sk_A)
% 0.82/1.06        | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.06        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.82/1.06        | (v2_struct_0 @ sk_B)
% 0.82/1.06        | (v2_struct_0 @ sk_A))),
% 0.82/1.06      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.82/1.06  thf('49', plain,
% 0.82/1.06      (((v2_struct_0 @ sk_B)
% 0.82/1.06        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.82/1.06        | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.06        | (v2_struct_0 @ sk_A))),
% 0.82/1.06      inference('simplify', [status(thm)], ['48'])).
% 0.82/1.06  thf('50', plain,
% 0.82/1.06      (![X29 : $i]:
% 0.82/1.06         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X29) @ sk_A @ sk_A)
% 0.82/1.06          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('51', plain,
% 0.82/1.06      (((v2_struct_0 @ sk_A)
% 0.82/1.06        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.82/1.06        | (v2_struct_0 @ sk_B)
% 0.82/1.06        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_D_2 @ sk_A)) @ sk_A @ sk_A))),
% 0.82/1.06      inference('sup-', [status(thm)], ['49', '50'])).
% 0.82/1.06  thf('52', plain,
% 0.82/1.06      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.82/1.06         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.82/1.06          | ~ (v5_pre_topc @ (k4_waybel_1 @ X27 @ (sk_D_2 @ X27)) @ X27 @ X27)
% 0.82/1.06          | ~ (v10_waybel_0 @ X28 @ X27)
% 0.82/1.06          | ~ (r3_waybel_9 @ X27 @ X28 @ X26)
% 0.82/1.06          | ((X26) = (k1_waybel_2 @ X27 @ X28))
% 0.82/1.06          | ~ (l1_waybel_0 @ X28 @ X27)
% 0.82/1.06          | ~ (v7_waybel_0 @ X28)
% 0.82/1.06          | ~ (v4_orders_2 @ X28)
% 0.82/1.06          | (v2_struct_0 @ X28)
% 0.82/1.06          | ~ (l1_waybel_9 @ X27)
% 0.82/1.06          | ~ (v1_compts_1 @ X27)
% 0.82/1.06          | ~ (v2_lattice3 @ X27)
% 0.82/1.06          | ~ (v1_lattice3 @ X27)
% 0.82/1.06          | ~ (v5_orders_2 @ X27)
% 0.82/1.06          | ~ (v4_orders_2 @ X27)
% 0.82/1.06          | ~ (v3_orders_2 @ X27)
% 0.82/1.06          | ~ (v8_pre_topc @ X27)
% 0.82/1.06          | ~ (v2_pre_topc @ X27))),
% 0.82/1.06      inference('cnf', [status(esa)], [t35_waybel_9])).
% 0.82/1.06  thf('53', plain,
% 0.82/1.06      (![X0 : $i, X1 : $i]:
% 0.82/1.06         ((v2_struct_0 @ sk_B)
% 0.82/1.06          | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.82/1.06          | (v2_struct_0 @ sk_A)
% 0.82/1.06          | ~ (v2_pre_topc @ sk_A)
% 0.82/1.06          | ~ (v8_pre_topc @ sk_A)
% 0.82/1.06          | ~ (v3_orders_2 @ sk_A)
% 0.82/1.06          | ~ (v4_orders_2 @ sk_A)
% 0.82/1.06          | ~ (v5_orders_2 @ sk_A)
% 0.82/1.06          | ~ (v1_lattice3 @ sk_A)
% 0.82/1.06          | ~ (v2_lattice3 @ sk_A)
% 0.82/1.06          | ~ (v1_compts_1 @ sk_A)
% 0.82/1.06          | ~ (l1_waybel_9 @ sk_A)
% 0.82/1.06          | (v2_struct_0 @ X0)
% 0.82/1.06          | ~ (v4_orders_2 @ X0)
% 0.82/1.06          | ~ (v7_waybel_0 @ X0)
% 0.82/1.06          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.82/1.06          | ((X1) = (k1_waybel_2 @ sk_A @ X0))
% 0.82/1.06          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 0.82/1.06          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.82/1.06          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.06      inference('sup-', [status(thm)], ['51', '52'])).
% 0.82/1.06  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('55', plain, ((v8_pre_topc @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('56', plain, ((v3_orders_2 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('57', plain, ((v4_orders_2 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('58', plain, ((v5_orders_2 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('59', plain, ((v1_lattice3 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('60', plain, ((v2_lattice3 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('61', plain, ((v1_compts_1 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('62', plain, ((l1_waybel_9 @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('63', plain,
% 0.82/1.06      (![X0 : $i, X1 : $i]:
% 0.82/1.06         ((v2_struct_0 @ sk_B)
% 0.82/1.06          | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.82/1.06          | (v2_struct_0 @ sk_A)
% 0.82/1.06          | (v2_struct_0 @ X0)
% 0.82/1.06          | ~ (v4_orders_2 @ X0)
% 0.82/1.06          | ~ (v7_waybel_0 @ X0)
% 0.82/1.06          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.82/1.06          | ((X1) = (k1_waybel_2 @ sk_A @ X0))
% 0.82/1.06          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 0.82/1.06          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.82/1.06          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.82/1.06      inference('demod', [status(thm)],
% 0.82/1.06                ['53', '54', '55', '56', '57', '58', '59', '60', '61', '62'])).
% 0.82/1.06  thf('64', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         ((v2_struct_0 @ sk_A)
% 0.82/1.06          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.82/1.06          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.82/1.06          | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 0.82/1.06          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.82/1.06          | ~ (v7_waybel_0 @ X0)
% 0.82/1.06          | ~ (v4_orders_2 @ X0)
% 0.82/1.06          | (v2_struct_0 @ X0)
% 0.82/1.06          | (v2_struct_0 @ sk_A)
% 0.82/1.06          | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.82/1.06          | (v2_struct_0 @ sk_B))),
% 0.82/1.06      inference('sup-', [status(thm)], ['28', '63'])).
% 0.82/1.06  thf('65', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         ((v2_struct_0 @ sk_B)
% 0.82/1.06          | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.82/1.06          | (v2_struct_0 @ X0)
% 0.82/1.06          | ~ (v4_orders_2 @ X0)
% 0.82/1.06          | ~ (v7_waybel_0 @ X0)
% 0.82/1.06          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.82/1.06          | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 0.82/1.06          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.82/1.06          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.82/1.06          | (v2_struct_0 @ sk_A))),
% 0.82/1.06      inference('simplify', [status(thm)], ['64'])).
% 0.82/1.06  thf('66', plain,
% 0.82/1.06      (((v2_struct_0 @ sk_A)
% 0.82/1.06        | (v2_struct_0 @ sk_A)
% 0.82/1.06        | ~ (v10_waybel_0 @ sk_B @ sk_A)
% 0.82/1.06        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.82/1.06        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.82/1.06        | ~ (v7_waybel_0 @ sk_B)
% 0.82/1.06        | ~ (v4_orders_2 @ sk_B)
% 0.82/1.06        | (v2_struct_0 @ sk_B)
% 0.82/1.06        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.82/1.06        | (v2_struct_0 @ sk_B))),
% 0.82/1.06      inference('sup-', [status(thm)], ['16', '65'])).
% 0.82/1.06  thf('67', plain, ((v10_waybel_0 @ sk_B @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('68', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('69', plain, ((v7_waybel_0 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('70', plain, ((v4_orders_2 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('71', plain,
% 0.82/1.06      (((v2_struct_0 @ sk_A)
% 0.82/1.06        | (v2_struct_0 @ sk_A)
% 0.82/1.06        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.82/1.06        | (v2_struct_0 @ sk_B)
% 0.82/1.06        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.82/1.06        | (v2_struct_0 @ sk_B))),
% 0.82/1.06      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 0.82/1.06  thf('72', plain,
% 0.82/1.06      (((v2_struct_0 @ sk_B)
% 0.82/1.06        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.82/1.06        | (v2_struct_0 @ sk_A))),
% 0.82/1.06      inference('simplify', [status(thm)], ['71'])).
% 0.82/1.06  thf('73', plain, (~ (v2_struct_0 @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('74', plain,
% 0.82/1.06      (((v2_struct_0 @ sk_A)
% 0.82/1.06        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.82/1.06      inference('clc', [status(thm)], ['72', '73'])).
% 0.82/1.06  thf('75', plain,
% 0.82/1.06      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.06        | (v2_struct_0 @ sk_A))),
% 0.82/1.06      inference('clc', [status(thm)], ['26', '27'])).
% 0.82/1.06  thf('76', plain,
% 0.82/1.06      (((m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.82/1.06        | (v2_struct_0 @ sk_A)
% 0.82/1.06        | (v2_struct_0 @ sk_A))),
% 0.82/1.06      inference('sup+', [status(thm)], ['74', '75'])).
% 0.82/1.06  thf('77', plain,
% 0.82/1.06      (((v2_struct_0 @ sk_A)
% 0.82/1.06        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.06      inference('simplify', [status(thm)], ['76'])).
% 0.82/1.06  thf('78', plain,
% 0.82/1.06      (((v2_struct_0 @ sk_A)
% 0.82/1.06        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.82/1.06      inference('clc', [status(thm)], ['72', '73'])).
% 0.82/1.06  thf('79', plain,
% 0.82/1.06      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.82/1.06        | (v2_struct_0 @ sk_A))),
% 0.82/1.06      inference('clc', [status(thm)], ['14', '15'])).
% 0.82/1.06  thf('80', plain,
% 0.82/1.06      (((r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_2 @ sk_A @ sk_B))
% 0.82/1.06        | (v2_struct_0 @ sk_A)
% 0.82/1.06        | (v2_struct_0 @ sk_A))),
% 0.82/1.06      inference('sup+', [status(thm)], ['78', '79'])).
% 0.82/1.06  thf('81', plain,
% 0.82/1.06      (((v2_struct_0 @ sk_A)
% 0.82/1.06        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.82/1.06      inference('simplify', [status(thm)], ['80'])).
% 0.82/1.06  thf('82', plain,
% 0.82/1.06      (((v2_struct_0 @ sk_A)
% 0.82/1.06        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.06      inference('simplify', [status(thm)], ['76'])).
% 0.82/1.06  thf('83', plain,
% 0.82/1.06      (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.82/1.06      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.82/1.06  thf('84', plain,
% 0.82/1.06      (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.82/1.06      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.82/1.06  thf('85', plain,
% 0.82/1.06      (((v2_struct_0 @ sk_A)
% 0.82/1.06        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.82/1.06      inference('simplify', [status(thm)], ['76'])).
% 0.82/1.06  thf('86', plain,
% 0.82/1.06      (((v2_struct_0 @ sk_A)
% 0.82/1.06        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.82/1.06      inference('clc', [status(thm)], ['72', '73'])).
% 0.82/1.06  thf('87', plain,
% 0.82/1.06      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.82/1.06        | (v2_struct_0 @ sk_A))),
% 0.82/1.06      inference('clc', [status(thm)], ['14', '15'])).
% 0.82/1.06  thf('88', plain,
% 0.82/1.06      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.06        | (v2_struct_0 @ sk_A))),
% 0.82/1.06      inference('clc', [status(thm)], ['26', '27'])).
% 0.82/1.06  thf(l48_waybel_9, axiom,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.82/1.06         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.82/1.06         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.82/1.06       ( ![B:$i]:
% 0.82/1.06         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.82/1.06             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.82/1.06           ( ![C:$i]:
% 0.82/1.06             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.06               ( ![D:$i]:
% 0.82/1.06                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.06                   ( ( ( ( C ) = ( D ) ) & 
% 0.82/1.06                       ( ![E:$i]:
% 0.82/1.06                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.82/1.06                           ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) ) ) & 
% 0.82/1.06                       ( v10_waybel_0 @ B @ A ) & ( r3_waybel_9 @ A @ B @ C ) ) =>
% 0.82/1.06                     ( r2_lattice3 @
% 0.82/1.06                       A @ 
% 0.82/1.06                       ( k2_relset_1 @
% 0.82/1.06                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.82/1.06                         ( u1_waybel_0 @ A @ B ) ) @ 
% 0.82/1.06                       D ) ) ) ) ) ) ) ) ))).
% 0.82/1.06  thf('89', plain,
% 0.82/1.06      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.82/1.06         ((v2_struct_0 @ X12)
% 0.82/1.06          | ~ (v4_orders_2 @ X12)
% 0.82/1.06          | ~ (v7_waybel_0 @ X12)
% 0.82/1.06          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.82/1.06          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.82/1.06          | (r2_lattice3 @ X13 @ 
% 0.82/1.06             (k2_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X13) @ 
% 0.82/1.06              (u1_waybel_0 @ X13 @ X12)) @ 
% 0.82/1.06             X14)
% 0.82/1.06          | ((X15) != (X14))
% 0.82/1.06          | ~ (r3_waybel_9 @ X13 @ X12 @ X15)
% 0.82/1.06          | ~ (v10_waybel_0 @ X12 @ X13)
% 0.82/1.06          | (m1_subset_1 @ (sk_E @ X13) @ (u1_struct_0 @ X13))
% 0.82/1.06          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.82/1.06          | ~ (l1_waybel_9 @ X13)
% 0.82/1.06          | ~ (v1_compts_1 @ X13)
% 0.82/1.06          | ~ (v2_lattice3 @ X13)
% 0.82/1.06          | ~ (v1_lattice3 @ X13)
% 0.82/1.06          | ~ (v5_orders_2 @ X13)
% 0.82/1.06          | ~ (v4_orders_2 @ X13)
% 0.82/1.06          | ~ (v3_orders_2 @ X13)
% 0.82/1.06          | ~ (v8_pre_topc @ X13)
% 0.82/1.06          | ~ (v2_pre_topc @ X13))),
% 0.82/1.06      inference('cnf', [status(esa)], [l48_waybel_9])).
% 0.82/1.06  thf('90', plain,
% 0.82/1.06      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.82/1.06         (~ (v2_pre_topc @ X13)
% 0.82/1.06          | ~ (v8_pre_topc @ X13)
% 0.82/1.06          | ~ (v3_orders_2 @ X13)
% 0.82/1.06          | ~ (v4_orders_2 @ X13)
% 0.82/1.06          | ~ (v5_orders_2 @ X13)
% 0.82/1.06          | ~ (v1_lattice3 @ X13)
% 0.82/1.06          | ~ (v2_lattice3 @ X13)
% 0.82/1.06          | ~ (v1_compts_1 @ X13)
% 0.82/1.06          | ~ (l1_waybel_9 @ X13)
% 0.82/1.06          | (m1_subset_1 @ (sk_E @ X13) @ (u1_struct_0 @ X13))
% 0.82/1.06          | ~ (v10_waybel_0 @ X12 @ X13)
% 0.82/1.06          | ~ (r3_waybel_9 @ X13 @ X12 @ X14)
% 0.82/1.06          | (r2_lattice3 @ X13 @ 
% 0.82/1.06             (k2_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X13) @ 
% 0.82/1.06              (u1_waybel_0 @ X13 @ X12)) @ 
% 0.82/1.06             X14)
% 0.82/1.06          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.82/1.06          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.82/1.06          | ~ (v7_waybel_0 @ X12)
% 0.82/1.06          | ~ (v4_orders_2 @ X12)
% 0.82/1.06          | (v2_struct_0 @ X12))),
% 0.82/1.06      inference('simplify', [status(thm)], ['89'])).
% 0.82/1.06  thf('91', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         ((v2_struct_0 @ sk_A)
% 0.82/1.06          | (v2_struct_0 @ X0)
% 0.82/1.06          | ~ (v4_orders_2 @ X0)
% 0.82/1.06          | ~ (v7_waybel_0 @ X0)
% 0.82/1.06          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.82/1.06          | (r2_lattice3 @ sk_A @ 
% 0.82/1.06             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.82/1.06              (u1_waybel_0 @ sk_A @ X0)) @ 
% 0.82/1.06             (sk_C_1 @ sk_B @ sk_A))
% 0.82/1.06          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.82/1.06          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.82/1.06          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.82/1.06          | ~ (l1_waybel_9 @ sk_A)
% 0.82/1.06          | ~ (v1_compts_1 @ sk_A)
% 0.82/1.06          | ~ (v2_lattice3 @ sk_A)
% 0.89/1.06          | ~ (v1_lattice3 @ sk_A)
% 0.89/1.06          | ~ (v5_orders_2 @ sk_A)
% 0.89/1.06          | ~ (v4_orders_2 @ sk_A)
% 0.89/1.06          | ~ (v3_orders_2 @ sk_A)
% 0.89/1.06          | ~ (v8_pre_topc @ sk_A)
% 0.89/1.06          | ~ (v2_pre_topc @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['88', '90'])).
% 0.89/1.06  thf('92', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('93', plain, ((v1_compts_1 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('94', plain, ((v2_lattice3 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('95', plain, ((v1_lattice3 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('96', plain, ((v5_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('97', plain, ((v4_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('98', plain, ((v3_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('99', plain, ((v8_pre_topc @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('101', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | (v2_struct_0 @ X0)
% 0.89/1.06          | ~ (v4_orders_2 @ X0)
% 0.89/1.06          | ~ (v7_waybel_0 @ X0)
% 0.89/1.06          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.06          | (r2_lattice3 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ X0)) @ 
% 0.89/1.06             (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.06          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.06          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.89/1.06          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('demod', [status(thm)],
% 0.89/1.06                ['91', '92', '93', '94', '95', '96', '97', '98', '99', '100'])).
% 0.89/1.06  thf('102', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | ~ (v10_waybel_0 @ sk_B @ sk_A)
% 0.89/1.06        | (r2_lattice3 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06           (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.06        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.89/1.06        | ~ (v7_waybel_0 @ sk_B)
% 0.89/1.06        | ~ (v4_orders_2 @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['87', '101'])).
% 0.89/1.06  thf('103', plain, ((v10_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('104', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('105', plain, ((v7_waybel_0 @ sk_B)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('106', plain, ((v4_orders_2 @ sk_B)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('107', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r2_lattice3 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06           (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('demod', [status(thm)], ['102', '103', '104', '105', '106'])).
% 0.89/1.06  thf('108', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_B)
% 0.89/1.06        | (r2_lattice3 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06           (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['107'])).
% 0.89/1.06  thf('109', plain,
% 0.89/1.06      (((r2_lattice3 @ sk_A @ 
% 0.89/1.06         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06         (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B))),
% 0.89/1.06      inference('sup+', [status(thm)], ['86', '108'])).
% 0.89/1.06  thf('110', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (r2_lattice3 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06           (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['109'])).
% 0.89/1.06  thf('111', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.06      inference('clc', [status(thm)], ['72', '73'])).
% 0.89/1.06  thf('112', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_B)
% 0.89/1.06        | (r2_lattice3 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06           (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['107'])).
% 0.89/1.06  thf('113', plain,
% 0.89/1.06      (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.89/1.06      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.89/1.06  thf('114', plain,
% 0.89/1.06      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('clc', [status(thm)], ['26', '27'])).
% 0.89/1.06  thf(t15_yellow_0, axiom,
% 0.89/1.06    (![A:$i]:
% 0.89/1.06     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.89/1.06       ( ![B:$i]:
% 0.89/1.06         ( ( r1_yellow_0 @ A @ B ) <=>
% 0.89/1.06           ( ?[C:$i]:
% 0.89/1.06             ( ( ![D:$i]:
% 0.89/1.06                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.89/1.06                   ( ( r2_lattice3 @ A @ B @ D ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) & 
% 0.89/1.06               ( r2_lattice3 @ A @ B @ C ) & 
% 0.89/1.06               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.89/1.06  thf('115', plain,
% 0.89/1.06      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.89/1.06         ((m1_subset_1 @ (sk_D @ X4 @ X5 @ X6) @ (u1_struct_0 @ X6))
% 0.89/1.06          | ~ (r2_lattice3 @ X6 @ X5 @ X4)
% 0.89/1.06          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X6))
% 0.89/1.06          | (r1_yellow_0 @ X6 @ X5)
% 0.89/1.06          | ~ (l1_orders_2 @ X6)
% 0.89/1.06          | ~ (v5_orders_2 @ X6))),
% 0.89/1.06      inference('cnf', [status(esa)], [t15_yellow_0])).
% 0.89/1.06  thf('116', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | ~ (v5_orders_2 @ sk_A)
% 0.89/1.06          | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ X0)
% 0.89/1.06          | ~ (r2_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.06          | (m1_subset_1 @ (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ X0 @ sk_A) @ 
% 0.89/1.06             (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['114', '115'])).
% 0.89/1.06  thf('117', plain, ((v5_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('118', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ X0)
% 0.89/1.06          | ~ (r2_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.06          | (m1_subset_1 @ (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ X0 @ sk_A) @ 
% 0.89/1.06             (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('demod', [status(thm)], ['116', '117'])).
% 0.89/1.06  thf('119', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         (~ (l1_waybel_9 @ sk_A)
% 0.89/1.06          | (m1_subset_1 @ (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ X0 @ sk_A) @ 
% 0.89/1.06             (u1_struct_0 @ sk_A))
% 0.89/1.06          | ~ (r2_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ X0)
% 0.89/1.06          | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['113', '118'])).
% 0.89/1.06  thf('120', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('121', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((m1_subset_1 @ (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ X0 @ sk_A) @ 
% 0.89/1.06           (u1_struct_0 @ sk_A))
% 0.89/1.06          | ~ (r2_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ X0)
% 0.89/1.06          | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('demod', [status(thm)], ['119', '120'])).
% 0.89/1.06  thf('122', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (m1_subset_1 @ 
% 0.89/1.06           (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A) @ 
% 0.89/1.06           (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['112', '121'])).
% 0.89/1.06  thf('123', plain,
% 0.89/1.06      (((m1_subset_1 @ 
% 0.89/1.06         (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.89/1.06          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06          sk_A) @ 
% 0.89/1.06         (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['122'])).
% 0.89/1.06  thf('124', plain,
% 0.89/1.06      (((m1_subset_1 @ 
% 0.89/1.06         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06          sk_A) @ 
% 0.89/1.06         (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B))))),
% 0.89/1.06      inference('sup+', [status(thm)], ['111', '123'])).
% 0.89/1.06  thf('125', plain,
% 0.89/1.06      (((r1_yellow_0 @ sk_A @ 
% 0.89/1.06         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06          (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ 
% 0.89/1.06           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A) @ 
% 0.89/1.06           (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['124'])).
% 0.89/1.06  thf('126', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['76'])).
% 0.89/1.06  thf('127', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['80'])).
% 0.89/1.06  thf('128', plain,
% 0.89/1.06      (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.89/1.06      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.89/1.06  thf('129', plain,
% 0.89/1.06      (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.89/1.06      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.89/1.06  thf('130', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['76'])).
% 0.89/1.06  thf('131', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (r2_lattice3 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06           (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['109'])).
% 0.89/1.06  thf('132', plain,
% 0.89/1.06      (((r1_yellow_0 @ sk_A @ 
% 0.89/1.06         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06          (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ 
% 0.89/1.06           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A) @ 
% 0.89/1.06           (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['124'])).
% 0.89/1.06  thf('133', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['76'])).
% 0.89/1.06  thf('134', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['80'])).
% 0.89/1.06  thf('135', plain,
% 0.89/1.06      (((r1_yellow_0 @ sk_A @ 
% 0.89/1.06         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06          (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ 
% 0.89/1.06           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A) @ 
% 0.89/1.06           (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['124'])).
% 0.89/1.06  thf('136', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.06      inference('clc', [status(thm)], ['72', '73'])).
% 0.89/1.06  thf('137', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_B)
% 0.89/1.06        | (r2_lattice3 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06           (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['107'])).
% 0.89/1.06  thf('138', plain,
% 0.89/1.06      (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.89/1.06      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.89/1.06  thf('139', plain,
% 0.89/1.06      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('clc', [status(thm)], ['26', '27'])).
% 0.89/1.06  thf('140', plain,
% 0.89/1.06      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.89/1.06         ((r2_lattice3 @ X6 @ X5 @ (sk_D @ X4 @ X5 @ X6))
% 0.89/1.06          | ~ (r2_lattice3 @ X6 @ X5 @ X4)
% 0.89/1.06          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X6))
% 0.89/1.06          | (r1_yellow_0 @ X6 @ X5)
% 0.89/1.06          | ~ (l1_orders_2 @ X6)
% 0.89/1.06          | ~ (v5_orders_2 @ X6))),
% 0.89/1.06      inference('cnf', [status(esa)], [t15_yellow_0])).
% 0.89/1.06  thf('141', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | ~ (v5_orders_2 @ sk_A)
% 0.89/1.06          | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ X0)
% 0.89/1.06          | ~ (r2_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.06          | (r2_lattice3 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ X0 @ sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['139', '140'])).
% 0.89/1.06  thf('142', plain, ((v5_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('143', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ X0)
% 0.89/1.06          | ~ (r2_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.06          | (r2_lattice3 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ X0 @ sk_A)))),
% 0.89/1.06      inference('demod', [status(thm)], ['141', '142'])).
% 0.89/1.06  thf('144', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         (~ (l1_waybel_9 @ sk_A)
% 0.89/1.06          | (r2_lattice3 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ X0 @ sk_A))
% 0.89/1.06          | ~ (r2_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ X0)
% 0.89/1.06          | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['138', '143'])).
% 0.89/1.06  thf('145', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('146', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((r2_lattice3 @ sk_A @ X0 @ 
% 0.89/1.06           (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ X0 @ sk_A))
% 0.89/1.06          | ~ (r2_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ X0)
% 0.89/1.06          | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('demod', [status(thm)], ['144', '145'])).
% 0.89/1.06  thf('147', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (r2_lattice3 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06           (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['137', '146'])).
% 0.89/1.06  thf('148', plain,
% 0.89/1.06      (((r2_lattice3 @ sk_A @ 
% 0.89/1.06         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06         (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.89/1.06          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06          sk_A))
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['147'])).
% 0.89/1.06  thf('149', plain,
% 0.89/1.06      (((r2_lattice3 @ sk_A @ 
% 0.89/1.06         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06          sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B))))),
% 0.89/1.06      inference('sup+', [status(thm)], ['136', '148'])).
% 0.89/1.06  thf('150', plain,
% 0.89/1.06      (((r1_yellow_0 @ sk_A @ 
% 0.89/1.06         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06          (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (r2_lattice3 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['149'])).
% 0.89/1.06  thf(l49_waybel_9, axiom,
% 0.89/1.06    (![A:$i]:
% 0.89/1.06     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.89/1.06         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.89/1.06         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.89/1.06       ( ![B:$i]:
% 0.89/1.06         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.89/1.06             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.89/1.06           ( ![C:$i]:
% 0.89/1.06             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.89/1.06               ( ![D:$i]:
% 0.89/1.06                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.89/1.06                   ( ( ( ( C ) = ( D ) ) & 
% 0.89/1.06                       ( ![E:$i]:
% 0.89/1.06                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.89/1.06                           ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) ) ) & 
% 0.89/1.06                       ( r3_waybel_9 @ A @ B @ C ) ) =>
% 0.89/1.06                     ( ![E:$i]:
% 0.89/1.06                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.89/1.06                         ( ( r2_lattice3 @
% 0.89/1.06                             A @ 
% 0.89/1.06                             ( k2_relset_1 @
% 0.89/1.06                               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.89/1.06                               ( u1_waybel_0 @ A @ B ) ) @ 
% 0.89/1.06                             E ) =>
% 0.89/1.06                           ( r3_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.89/1.06  thf('151', plain,
% 0.89/1.06      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.89/1.06         ((v2_struct_0 @ X16)
% 0.89/1.06          | ~ (v4_orders_2 @ X16)
% 0.89/1.06          | ~ (v7_waybel_0 @ X16)
% 0.89/1.06          | ~ (l1_waybel_0 @ X16 @ X17)
% 0.89/1.06          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.89/1.06          | ~ (r2_lattice3 @ X17 @ 
% 0.89/1.06               (k2_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.89/1.06                (u1_waybel_0 @ X17 @ X16)) @ 
% 0.89/1.06               X19)
% 0.89/1.06          | (r3_orders_2 @ X17 @ X18 @ X19)
% 0.89/1.06          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.89/1.06          | ((X20) != (X18))
% 0.89/1.06          | ~ (r3_waybel_9 @ X17 @ X16 @ X20)
% 0.89/1.06          | (m1_subset_1 @ (sk_E_1 @ X17) @ (u1_struct_0 @ X17))
% 0.89/1.06          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X17))
% 0.89/1.06          | ~ (l1_waybel_9 @ X17)
% 0.89/1.06          | ~ (v1_compts_1 @ X17)
% 0.89/1.06          | ~ (v2_lattice3 @ X17)
% 0.89/1.06          | ~ (v1_lattice3 @ X17)
% 0.89/1.06          | ~ (v5_orders_2 @ X17)
% 0.89/1.06          | ~ (v4_orders_2 @ X17)
% 0.89/1.06          | ~ (v3_orders_2 @ X17)
% 0.89/1.06          | ~ (v8_pre_topc @ X17)
% 0.89/1.06          | ~ (v2_pre_topc @ X17))),
% 0.89/1.06      inference('cnf', [status(esa)], [l49_waybel_9])).
% 0.89/1.06  thf('152', plain,
% 0.89/1.06      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.89/1.06         (~ (v2_pre_topc @ X17)
% 0.89/1.06          | ~ (v8_pre_topc @ X17)
% 0.89/1.06          | ~ (v3_orders_2 @ X17)
% 0.89/1.06          | ~ (v4_orders_2 @ X17)
% 0.89/1.06          | ~ (v5_orders_2 @ X17)
% 0.89/1.06          | ~ (v1_lattice3 @ X17)
% 0.89/1.06          | ~ (v2_lattice3 @ X17)
% 0.89/1.06          | ~ (v1_compts_1 @ X17)
% 0.89/1.06          | ~ (l1_waybel_9 @ X17)
% 0.89/1.06          | (m1_subset_1 @ (sk_E_1 @ X17) @ (u1_struct_0 @ X17))
% 0.89/1.06          | ~ (r3_waybel_9 @ X17 @ X16 @ X18)
% 0.89/1.06          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.89/1.06          | (r3_orders_2 @ X17 @ X18 @ X19)
% 0.89/1.06          | ~ (r2_lattice3 @ X17 @ 
% 0.89/1.06               (k2_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.89/1.06                (u1_waybel_0 @ X17 @ X16)) @ 
% 0.89/1.06               X19)
% 0.89/1.06          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.89/1.06          | ~ (l1_waybel_0 @ X16 @ X17)
% 0.89/1.06          | ~ (v7_waybel_0 @ X16)
% 0.89/1.06          | ~ (v4_orders_2 @ X16)
% 0.89/1.06          | (v2_struct_0 @ X16))),
% 0.89/1.06      inference('simplify', [status(thm)], ['151'])).
% 0.89/1.06  thf('153', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | ~ (v4_orders_2 @ sk_B)
% 0.89/1.06          | ~ (v7_waybel_0 @ sk_B)
% 0.89/1.06          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06              sk_A))
% 0.89/1.06          | ~ (m1_subset_1 @ 
% 0.89/1.06               (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06                sk_A) @ 
% 0.89/1.06               (u1_struct_0 @ sk_A))
% 0.89/1.06          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.06          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | ~ (l1_waybel_9 @ sk_A)
% 0.89/1.06          | ~ (v1_compts_1 @ sk_A)
% 0.89/1.06          | ~ (v2_lattice3 @ sk_A)
% 0.89/1.06          | ~ (v1_lattice3 @ sk_A)
% 0.89/1.06          | ~ (v5_orders_2 @ sk_A)
% 0.89/1.06          | ~ (v4_orders_2 @ sk_A)
% 0.89/1.06          | ~ (v3_orders_2 @ sk_A)
% 0.89/1.06          | ~ (v8_pre_topc @ sk_A)
% 0.89/1.06          | ~ (v2_pre_topc @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['150', '152'])).
% 0.89/1.06  thf('154', plain, ((v4_orders_2 @ sk_B)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('155', plain, ((v7_waybel_0 @ sk_B)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('156', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('157', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('158', plain, ((v1_compts_1 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('159', plain, ((v2_lattice3 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('160', plain, ((v1_lattice3 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('161', plain, ((v5_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('162', plain, ((v4_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('163', plain, ((v3_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('164', plain, ((v8_pre_topc @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('165', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('166', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06              sk_A))
% 0.89/1.06          | ~ (m1_subset_1 @ 
% 0.89/1.06               (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06                sk_A) @ 
% 0.89/1.06               (u1_struct_0 @ sk_A))
% 0.89/1.06          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.06          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('demod', [status(thm)],
% 0.89/1.06                ['153', '154', '155', '156', '157', '158', '159', '160', 
% 0.89/1.06                 '161', '162', '163', '164', '165'])).
% 0.89/1.06  thf('167', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.06          | ~ (m1_subset_1 @ 
% 0.89/1.06               (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06                sk_A) @ 
% 0.89/1.06               (u1_struct_0 @ sk_A))
% 0.89/1.06          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06              sk_A))
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['166'])).
% 0.89/1.06  thf('168', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06          | (v2_struct_0 @ sk_A)
% 0.89/1.06          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06              sk_A))
% 0.89/1.06          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.06          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['135', '167'])).
% 0.89/1.06  thf('169', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.06          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06              sk_A))
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['168'])).
% 0.89/1.06  thf('170', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A))
% 0.89/1.06        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['134', '169'])).
% 0.89/1.06  thf('171', plain,
% 0.89/1.06      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A))
% 0.89/1.06        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['170'])).
% 0.89/1.06  thf('172', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A))
% 0.89/1.06        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['133', '171'])).
% 0.89/1.06  thf('173', plain,
% 0.89/1.06      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A))
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['172'])).
% 0.89/1.06  thf('174', plain,
% 0.89/1.06      (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.89/1.06      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.89/1.06  thf('175', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['76'])).
% 0.89/1.06  thf(redefinition_r3_orders_2, axiom,
% 0.89/1.06    (![A:$i,B:$i,C:$i]:
% 0.89/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.89/1.06         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.89/1.06         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.06       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.89/1.06  thf('176', plain,
% 0.89/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.06         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.89/1.06          | ~ (l1_orders_2 @ X1)
% 0.89/1.06          | ~ (v3_orders_2 @ X1)
% 0.89/1.06          | (v2_struct_0 @ X1)
% 0.89/1.06          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.89/1.06          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.89/1.06          | ~ (r3_orders_2 @ X1 @ X0 @ X2))),
% 0.89/1.06      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.89/1.06  thf('177', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | ~ (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 0.89/1.06          | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (v2_struct_0 @ sk_A)
% 0.89/1.06          | ~ (v3_orders_2 @ sk_A)
% 0.89/1.06          | ~ (l1_orders_2 @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['175', '176'])).
% 0.89/1.06  thf('178', plain, ((v3_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('179', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | ~ (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 0.89/1.06          | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (v2_struct_0 @ sk_A)
% 0.89/1.06          | ~ (l1_orders_2 @ sk_A))),
% 0.89/1.06      inference('demod', [status(thm)], ['177', '178'])).
% 0.89/1.06  thf('180', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         (~ (l1_orders_2 @ sk_A)
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 0.89/1.06          | ~ (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 0.89/1.06          | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['179'])).
% 0.89/1.06  thf('181', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         (~ (l1_waybel_9 @ sk_A)
% 0.89/1.06          | (v2_struct_0 @ sk_A)
% 0.89/1.06          | ~ (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 0.89/1.06          | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['174', '180'])).
% 0.89/1.06  thf('182', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('183', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | ~ (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 0.89/1.06          | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('demod', [status(thm)], ['181', '182'])).
% 0.89/1.06  thf('184', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | ~ (m1_subset_1 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06              sk_A) @ 
% 0.89/1.06             (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['173', '183'])).
% 0.89/1.06  thf('185', plain,
% 0.89/1.06      (((r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06          sk_A))
% 0.89/1.06        | ~ (m1_subset_1 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06              sk_A) @ 
% 0.89/1.06             (u1_struct_0 @ sk_A))
% 0.89/1.06        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['184'])).
% 0.89/1.06  thf('186', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['132', '185'])).
% 0.89/1.06  thf('187', plain,
% 0.89/1.06      (((r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06          sk_A))
% 0.89/1.06        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['186'])).
% 0.89/1.06  thf('188', plain,
% 0.89/1.06      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.89/1.06         (~ (r1_orders_2 @ X6 @ X4 @ (sk_D @ X4 @ X5 @ X6))
% 0.89/1.06          | ~ (r2_lattice3 @ X6 @ X5 @ X4)
% 0.89/1.06          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X6))
% 0.89/1.06          | (r1_yellow_0 @ X6 @ X5)
% 0.89/1.06          | ~ (l1_orders_2 @ X6)
% 0.89/1.06          | ~ (v5_orders_2 @ X6))),
% 0.89/1.06      inference('cnf', [status(esa)], [t15_yellow_0])).
% 0.89/1.06  thf('189', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | ~ (v5_orders_2 @ sk_A)
% 0.89/1.06        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | ~ (r2_lattice3 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06             (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['187', '188'])).
% 0.89/1.06  thf('190', plain, ((v5_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('191', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | ~ (r2_lattice3 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06             (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.06      inference('demod', [status(thm)], ['189', '190'])).
% 0.89/1.06  thf('192', plain,
% 0.89/1.06      ((~ (r2_lattice3 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06           (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['191'])).
% 0.89/1.06  thf('193', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['131', '192'])).
% 0.89/1.06  thf('194', plain,
% 0.89/1.06      ((~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['193'])).
% 0.89/1.06  thf('195', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | ~ (l1_orders_2 @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['130', '194'])).
% 0.89/1.06  thf('196', plain,
% 0.89/1.06      ((~ (l1_orders_2 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['195'])).
% 0.89/1.06  thf('197', plain,
% 0.89/1.06      ((~ (l1_waybel_9 @ sk_A)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['129', '196'])).
% 0.89/1.06  thf('198', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('199', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('demod', [status(thm)], ['197', '198'])).
% 0.89/1.06  thf(d3_waybel_9, axiom,
% 0.89/1.06    (![A:$i]:
% 0.89/1.06     ( ( l1_orders_2 @ A ) =>
% 0.89/1.06       ( ![B:$i]:
% 0.89/1.06         ( ( l1_waybel_0 @ B @ A ) =>
% 0.89/1.06           ( ( r1_waybel_9 @ A @ B ) <=>
% 0.89/1.06             ( r1_yellow_0 @
% 0.89/1.06               A @ 
% 0.89/1.06               ( k2_relset_1 @
% 0.89/1.06                 ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.89/1.06                 ( u1_waybel_0 @ A @ B ) ) ) ) ) ) ))).
% 0.89/1.06  thf('200', plain,
% 0.89/1.06      (![X9 : $i, X10 : $i]:
% 0.89/1.06         (~ (l1_waybel_0 @ X9 @ X10)
% 0.89/1.06          | ~ (r1_yellow_0 @ X10 @ 
% 0.89/1.06               (k2_relset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X10) @ 
% 0.89/1.06                (u1_waybel_0 @ X10 @ X9)))
% 0.89/1.06          | (r1_waybel_9 @ X10 @ X9)
% 0.89/1.06          | ~ (l1_orders_2 @ X10))),
% 0.89/1.06      inference('cnf', [status(esa)], [d3_waybel_9])).
% 0.89/1.06  thf('201', plain,
% 0.89/1.06      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['199', '200'])).
% 0.89/1.06  thf('202', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('203', plain,
% 0.89/1.06      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B))),
% 0.89/1.06      inference('demod', [status(thm)], ['201', '202'])).
% 0.89/1.06  thf('204', plain,
% 0.89/1.06      ((~ (l1_waybel_9 @ sk_A)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['128', '203'])).
% 0.89/1.06  thf('205', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('206', plain,
% 0.89/1.06      (((r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('demod', [status(thm)], ['204', '205'])).
% 0.89/1.06  thf('207', plain,
% 0.89/1.06      (![X29 : $i]:
% 0.89/1.06         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X29) @ sk_A @ sk_A)
% 0.89/1.06          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('208', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['206', '207'])).
% 0.89/1.06  thf('209', plain,
% 0.89/1.06      (((r1_yellow_0 @ sk_A @ 
% 0.89/1.06         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06          (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ 
% 0.89/1.06           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A) @ 
% 0.89/1.06           (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['124'])).
% 0.89/1.06  thf('210', plain,
% 0.89/1.06      (((r1_yellow_0 @ sk_A @ 
% 0.89/1.06         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06          (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (r2_lattice3 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['149'])).
% 0.89/1.06  thf('211', plain,
% 0.89/1.06      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.89/1.06         ((v2_struct_0 @ X16)
% 0.89/1.06          | ~ (v4_orders_2 @ X16)
% 0.89/1.06          | ~ (v7_waybel_0 @ X16)
% 0.89/1.06          | ~ (l1_waybel_0 @ X16 @ X17)
% 0.89/1.06          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.89/1.06          | ~ (r2_lattice3 @ X17 @ 
% 0.89/1.06               (k2_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.89/1.06                (u1_waybel_0 @ X17 @ X16)) @ 
% 0.89/1.06               X19)
% 0.89/1.06          | (r3_orders_2 @ X17 @ X18 @ X19)
% 0.89/1.06          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.89/1.06          | ((X20) != (X18))
% 0.89/1.06          | ~ (r3_waybel_9 @ X17 @ X16 @ X20)
% 0.89/1.06          | ~ (v5_pre_topc @ (k4_waybel_1 @ X17 @ (sk_E_1 @ X17)) @ X17 @ X17)
% 0.89/1.06          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X17))
% 0.89/1.06          | ~ (l1_waybel_9 @ X17)
% 0.89/1.06          | ~ (v1_compts_1 @ X17)
% 0.89/1.06          | ~ (v2_lattice3 @ X17)
% 0.89/1.06          | ~ (v1_lattice3 @ X17)
% 0.89/1.06          | ~ (v5_orders_2 @ X17)
% 0.89/1.06          | ~ (v4_orders_2 @ X17)
% 0.89/1.06          | ~ (v3_orders_2 @ X17)
% 0.89/1.06          | ~ (v8_pre_topc @ X17)
% 0.89/1.06          | ~ (v2_pre_topc @ X17))),
% 0.89/1.06      inference('cnf', [status(esa)], [l49_waybel_9])).
% 0.89/1.06  thf('212', plain,
% 0.89/1.06      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.89/1.06         (~ (v2_pre_topc @ X17)
% 0.89/1.06          | ~ (v8_pre_topc @ X17)
% 0.89/1.06          | ~ (v3_orders_2 @ X17)
% 0.89/1.06          | ~ (v4_orders_2 @ X17)
% 0.89/1.06          | ~ (v5_orders_2 @ X17)
% 0.89/1.06          | ~ (v1_lattice3 @ X17)
% 0.89/1.06          | ~ (v2_lattice3 @ X17)
% 0.89/1.06          | ~ (v1_compts_1 @ X17)
% 0.89/1.06          | ~ (l1_waybel_9 @ X17)
% 0.89/1.06          | ~ (v5_pre_topc @ (k4_waybel_1 @ X17 @ (sk_E_1 @ X17)) @ X17 @ X17)
% 0.89/1.06          | ~ (r3_waybel_9 @ X17 @ X16 @ X18)
% 0.89/1.06          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.89/1.06          | (r3_orders_2 @ X17 @ X18 @ X19)
% 0.89/1.06          | ~ (r2_lattice3 @ X17 @ 
% 0.89/1.06               (k2_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.89/1.06                (u1_waybel_0 @ X17 @ X16)) @ 
% 0.89/1.06               X19)
% 0.89/1.06          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.89/1.06          | ~ (l1_waybel_0 @ X16 @ X17)
% 0.89/1.06          | ~ (v7_waybel_0 @ X16)
% 0.89/1.06          | ~ (v4_orders_2 @ X16)
% 0.89/1.06          | (v2_struct_0 @ X16))),
% 0.89/1.06      inference('simplify', [status(thm)], ['211'])).
% 0.89/1.06  thf('213', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | ~ (v4_orders_2 @ sk_B)
% 0.89/1.06          | ~ (v7_waybel_0 @ sk_B)
% 0.89/1.06          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06              sk_A))
% 0.89/1.06          | ~ (m1_subset_1 @ 
% 0.89/1.06               (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06                sk_A) @ 
% 0.89/1.06               (u1_struct_0 @ sk_A))
% 0.89/1.06          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.06          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 0.89/1.06               sk_A)
% 0.89/1.06          | ~ (l1_waybel_9 @ sk_A)
% 0.89/1.06          | ~ (v1_compts_1 @ sk_A)
% 0.89/1.06          | ~ (v2_lattice3 @ sk_A)
% 0.89/1.06          | ~ (v1_lattice3 @ sk_A)
% 0.89/1.06          | ~ (v5_orders_2 @ sk_A)
% 0.89/1.06          | ~ (v4_orders_2 @ sk_A)
% 0.89/1.06          | ~ (v3_orders_2 @ sk_A)
% 0.89/1.06          | ~ (v8_pre_topc @ sk_A)
% 0.89/1.06          | ~ (v2_pre_topc @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['210', '212'])).
% 0.89/1.06  thf('214', plain, ((v4_orders_2 @ sk_B)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('215', plain, ((v7_waybel_0 @ sk_B)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('216', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('217', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('218', plain, ((v1_compts_1 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('219', plain, ((v2_lattice3 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('220', plain, ((v1_lattice3 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('221', plain, ((v5_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('222', plain, ((v4_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('223', plain, ((v3_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('224', plain, ((v8_pre_topc @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('225', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('226', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06              sk_A))
% 0.89/1.06          | ~ (m1_subset_1 @ 
% 0.89/1.06               (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06                sk_A) @ 
% 0.89/1.06               (u1_struct_0 @ sk_A))
% 0.89/1.06          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.06          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 0.89/1.06               sk_A))),
% 0.89/1.06      inference('demod', [status(thm)],
% 0.89/1.06                ['213', '214', '215', '216', '217', '218', '219', '220', 
% 0.89/1.06                 '221', '222', '223', '224', '225'])).
% 0.89/1.06  thf('227', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         (~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 0.89/1.06          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.06          | ~ (m1_subset_1 @ 
% 0.89/1.06               (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06                sk_A) @ 
% 0.89/1.06               (u1_struct_0 @ sk_A))
% 0.89/1.06          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06              sk_A))
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['226'])).
% 0.89/1.06  thf('228', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06          | (v2_struct_0 @ sk_A)
% 0.89/1.06          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06              sk_A))
% 0.89/1.06          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.06          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 0.89/1.06               sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['209', '227'])).
% 0.89/1.06  thf('229', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         (~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 0.89/1.06          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.06          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06              sk_A))
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['228'])).
% 0.89/1.06  thf('230', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06          | (v2_struct_0 @ sk_A)
% 0.89/1.06          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (v2_struct_0 @ sk_A)
% 0.89/1.06          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06              sk_A))
% 0.89/1.06          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0))),
% 0.89/1.06      inference('sup-', [status(thm)], ['208', '229'])).
% 0.89/1.06  thf('231', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         (~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.06          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06              sk_A))
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (v2_struct_0 @ sk_A)
% 0.89/1.06          | (r1_waybel_9 @ sk_A @ sk_B))),
% 0.89/1.06      inference('simplify', [status(thm)], ['230'])).
% 0.89/1.06  thf('232', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['127', '231'])).
% 0.89/1.06  thf('233', plain,
% 0.89/1.06      (((r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06          sk_A))
% 0.89/1.06        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['232'])).
% 0.89/1.06  thf('234', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['126', '233'])).
% 0.89/1.06  thf('235', plain,
% 0.89/1.06      (((r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06          sk_A))
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['234'])).
% 0.89/1.06  thf('236', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | ~ (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 0.89/1.06          | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('demod', [status(thm)], ['181', '182'])).
% 0.89/1.06  thf('237', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | ~ (m1_subset_1 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06              sk_A) @ 
% 0.89/1.06             (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['235', '236'])).
% 0.89/1.06  thf('238', plain,
% 0.89/1.06      (((r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06          sk_A))
% 0.89/1.06        | ~ (m1_subset_1 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06              sk_A) @ 
% 0.89/1.06             (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['237'])).
% 0.89/1.06  thf('239', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['125', '238'])).
% 0.89/1.06  thf('240', plain,
% 0.89/1.06      (((r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06          sk_A))
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['239'])).
% 0.89/1.06  thf('241', plain,
% 0.89/1.06      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.89/1.06         (~ (r1_orders_2 @ X6 @ X4 @ (sk_D @ X4 @ X5 @ X6))
% 0.89/1.06          | ~ (r2_lattice3 @ X6 @ X5 @ X4)
% 0.89/1.06          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X6))
% 0.89/1.06          | (r1_yellow_0 @ X6 @ X5)
% 0.89/1.06          | ~ (l1_orders_2 @ X6)
% 0.89/1.06          | ~ (v5_orders_2 @ X6))),
% 0.89/1.06      inference('cnf', [status(esa)], [t15_yellow_0])).
% 0.89/1.06  thf('242', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | ~ (v5_orders_2 @ sk_A)
% 0.89/1.06        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | ~ (r2_lattice3 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06             (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['240', '241'])).
% 0.89/1.06  thf('243', plain, ((v5_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('244', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | ~ (r2_lattice3 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06             (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.06      inference('demod', [status(thm)], ['242', '243'])).
% 0.89/1.06  thf('245', plain,
% 0.89/1.06      ((~ (r2_lattice3 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06           (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['244'])).
% 0.89/1.06  thf('246', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['110', '245'])).
% 0.89/1.06  thf('247', plain,
% 0.89/1.06      ((~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['246'])).
% 0.89/1.06  thf('248', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | ~ (l1_orders_2 @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['85', '247'])).
% 0.89/1.06  thf('249', plain,
% 0.89/1.06      ((~ (l1_orders_2 @ sk_A)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['248'])).
% 0.89/1.06  thf('250', plain,
% 0.89/1.06      ((~ (l1_waybel_9 @ sk_A)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B))),
% 0.89/1.06      inference('sup-', [status(thm)], ['84', '249'])).
% 0.89/1.06  thf('251', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('252', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B))),
% 0.89/1.06      inference('demod', [status(thm)], ['250', '251'])).
% 0.89/1.06  thf('253', plain,
% 0.89/1.06      (![X9 : $i, X10 : $i]:
% 0.89/1.06         (~ (l1_waybel_0 @ X9 @ X10)
% 0.89/1.06          | ~ (r1_yellow_0 @ X10 @ 
% 0.89/1.06               (k2_relset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X10) @ 
% 0.89/1.06                (u1_waybel_0 @ X10 @ X9)))
% 0.89/1.06          | (r1_waybel_9 @ X10 @ X9)
% 0.89/1.06          | ~ (l1_orders_2 @ X10))),
% 0.89/1.06      inference('cnf', [status(esa)], [d3_waybel_9])).
% 0.89/1.06  thf('254', plain,
% 0.89/1.06      (((r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['252', '253'])).
% 0.89/1.06  thf('255', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('256', plain,
% 0.89/1.06      (((r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B))),
% 0.89/1.06      inference('demod', [status(thm)], ['254', '255'])).
% 0.89/1.06  thf('257', plain,
% 0.89/1.06      ((~ (l1_orders_2 @ sk_A)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B))),
% 0.89/1.06      inference('simplify', [status(thm)], ['256'])).
% 0.89/1.06  thf('258', plain,
% 0.89/1.06      ((~ (l1_waybel_9 @ sk_A)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['83', '257'])).
% 0.89/1.06  thf('259', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('260', plain,
% 0.89/1.06      (((r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('demod', [status(thm)], ['258', '259'])).
% 0.89/1.06  thf('261', plain,
% 0.89/1.06      (![X29 : $i]:
% 0.89/1.06         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X29) @ sk_A @ sk_A)
% 0.89/1.06          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('262', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E @ sk_A)) @ sk_A @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['260', '261'])).
% 0.89/1.06  thf('263', plain,
% 0.89/1.06      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.89/1.06         ((v2_struct_0 @ X12)
% 0.89/1.06          | ~ (v4_orders_2 @ X12)
% 0.89/1.06          | ~ (v7_waybel_0 @ X12)
% 0.89/1.06          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.89/1.06          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.89/1.06          | (r2_lattice3 @ X13 @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X13) @ 
% 0.89/1.06              (u1_waybel_0 @ X13 @ X12)) @ 
% 0.89/1.06             X14)
% 0.89/1.06          | ((X15) != (X14))
% 0.89/1.06          | ~ (r3_waybel_9 @ X13 @ X12 @ X15)
% 0.89/1.06          | ~ (v10_waybel_0 @ X12 @ X13)
% 0.89/1.06          | ~ (v5_pre_topc @ (k4_waybel_1 @ X13 @ (sk_E @ X13)) @ X13 @ X13)
% 0.89/1.06          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.89/1.06          | ~ (l1_waybel_9 @ X13)
% 0.89/1.06          | ~ (v1_compts_1 @ X13)
% 0.89/1.06          | ~ (v2_lattice3 @ X13)
% 0.89/1.06          | ~ (v1_lattice3 @ X13)
% 0.89/1.06          | ~ (v5_orders_2 @ X13)
% 0.89/1.06          | ~ (v4_orders_2 @ X13)
% 0.89/1.06          | ~ (v3_orders_2 @ X13)
% 0.89/1.06          | ~ (v8_pre_topc @ X13)
% 0.89/1.06          | ~ (v2_pre_topc @ X13))),
% 0.89/1.06      inference('cnf', [status(esa)], [l48_waybel_9])).
% 0.89/1.06  thf('264', plain,
% 0.89/1.06      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.89/1.06         (~ (v2_pre_topc @ X13)
% 0.89/1.06          | ~ (v8_pre_topc @ X13)
% 0.89/1.06          | ~ (v3_orders_2 @ X13)
% 0.89/1.06          | ~ (v4_orders_2 @ X13)
% 0.89/1.06          | ~ (v5_orders_2 @ X13)
% 0.89/1.06          | ~ (v1_lattice3 @ X13)
% 0.89/1.06          | ~ (v2_lattice3 @ X13)
% 0.89/1.06          | ~ (v1_compts_1 @ X13)
% 0.89/1.06          | ~ (l1_waybel_9 @ X13)
% 0.89/1.06          | ~ (v5_pre_topc @ (k4_waybel_1 @ X13 @ (sk_E @ X13)) @ X13 @ X13)
% 0.89/1.06          | ~ (v10_waybel_0 @ X12 @ X13)
% 0.89/1.06          | ~ (r3_waybel_9 @ X13 @ X12 @ X14)
% 0.89/1.06          | (r2_lattice3 @ X13 @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X13) @ 
% 0.89/1.06              (u1_waybel_0 @ X13 @ X12)) @ 
% 0.89/1.06             X14)
% 0.89/1.06          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.89/1.06          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.89/1.06          | ~ (v7_waybel_0 @ X12)
% 0.89/1.06          | ~ (v4_orders_2 @ X12)
% 0.89/1.06          | (v2_struct_0 @ X12))),
% 0.89/1.06      inference('simplify', [status(thm)], ['263'])).
% 0.89/1.06  thf('265', plain,
% 0.89/1.06      (![X0 : $i, X1 : $i]:
% 0.89/1.06         ((r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (v2_struct_0 @ sk_A)
% 0.89/1.06          | (v2_struct_0 @ X0)
% 0.89/1.06          | ~ (v4_orders_2 @ X0)
% 0.89/1.06          | ~ (v7_waybel_0 @ X0)
% 0.89/1.06          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.06          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (r2_lattice3 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ X0)) @ 
% 0.89/1.06             X1)
% 0.89/1.06          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 0.89/1.06          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.89/1.06          | ~ (l1_waybel_9 @ sk_A)
% 0.89/1.06          | ~ (v1_compts_1 @ sk_A)
% 0.89/1.06          | ~ (v2_lattice3 @ sk_A)
% 0.89/1.06          | ~ (v1_lattice3 @ sk_A)
% 0.89/1.06          | ~ (v5_orders_2 @ sk_A)
% 0.89/1.06          | ~ (v4_orders_2 @ sk_A)
% 0.89/1.06          | ~ (v3_orders_2 @ sk_A)
% 0.89/1.06          | ~ (v8_pre_topc @ sk_A)
% 0.89/1.06          | ~ (v2_pre_topc @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['262', '264'])).
% 0.89/1.06  thf('266', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('267', plain, ((v1_compts_1 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('268', plain, ((v2_lattice3 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('269', plain, ((v1_lattice3 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('270', plain, ((v5_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('271', plain, ((v4_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('272', plain, ((v3_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('273', plain, ((v8_pre_topc @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('274', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('275', plain,
% 0.89/1.06      (![X0 : $i, X1 : $i]:
% 0.89/1.06         ((r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (v2_struct_0 @ sk_A)
% 0.89/1.06          | (v2_struct_0 @ X0)
% 0.89/1.06          | ~ (v4_orders_2 @ X0)
% 0.89/1.06          | ~ (v7_waybel_0 @ X0)
% 0.89/1.06          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.06          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (r2_lattice3 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ X0)) @ 
% 0.89/1.06             X1)
% 0.89/1.06          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 0.89/1.06          | ~ (v10_waybel_0 @ X0 @ sk_A))),
% 0.89/1.06      inference('demod', [status(thm)],
% 0.89/1.06                ['265', '266', '267', '268', '269', '270', '271', '272', 
% 0.89/1.06                 '273', '274'])).
% 0.89/1.06  thf('276', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.89/1.06          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06          | (r2_lattice3 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ X0)) @ 
% 0.89/1.06             (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.06          | ~ (v7_waybel_0 @ X0)
% 0.89/1.06          | ~ (v4_orders_2 @ X0)
% 0.89/1.06          | (v2_struct_0 @ X0)
% 0.89/1.06          | (v2_struct_0 @ sk_A)
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (r1_waybel_9 @ sk_A @ sk_B))),
% 0.89/1.06      inference('sup-', [status(thm)], ['82', '275'])).
% 0.89/1.06  thf('277', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (v2_struct_0 @ X0)
% 0.89/1.06          | ~ (v4_orders_2 @ X0)
% 0.89/1.06          | ~ (v7_waybel_0 @ X0)
% 0.89/1.06          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.06          | (r2_lattice3 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ X0)) @ 
% 0.89/1.06             (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.89/1.06          | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['276'])).
% 0.89/1.06  thf('278', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | ~ (v10_waybel_0 @ sk_B @ sk_A)
% 0.89/1.06        | (r2_lattice3 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06           (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.89/1.06        | ~ (v7_waybel_0 @ sk_B)
% 0.89/1.06        | ~ (v4_orders_2 @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B))),
% 0.89/1.06      inference('sup-', [status(thm)], ['81', '277'])).
% 0.89/1.06  thf('279', plain, ((v10_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('280', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('281', plain, ((v7_waybel_0 @ sk_B)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('282', plain, ((v4_orders_2 @ sk_B)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('283', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (r2_lattice3 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06           (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B))),
% 0.89/1.06      inference('demod', [status(thm)], ['278', '279', '280', '281', '282'])).
% 0.89/1.06  thf('284', plain,
% 0.89/1.06      (((r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r2_lattice3 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06           (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['283'])).
% 0.89/1.06  thf('285', plain,
% 0.89/1.06      (((r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r2_lattice3 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06           (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['283'])).
% 0.89/1.06  thf('286', plain,
% 0.89/1.06      (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.89/1.06      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.89/1.06  thf('287', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['76'])).
% 0.89/1.06  thf('288', plain,
% 0.89/1.06      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.89/1.06         ((m1_subset_1 @ (sk_D @ X4 @ X5 @ X6) @ (u1_struct_0 @ X6))
% 0.89/1.06          | ~ (r2_lattice3 @ X6 @ X5 @ X4)
% 0.89/1.06          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X6))
% 0.89/1.06          | (r1_yellow_0 @ X6 @ X5)
% 0.89/1.06          | ~ (l1_orders_2 @ X6)
% 0.89/1.06          | ~ (v5_orders_2 @ X6))),
% 0.89/1.06      inference('cnf', [status(esa)], [t15_yellow_0])).
% 0.89/1.06  thf('289', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | ~ (v5_orders_2 @ sk_A)
% 0.89/1.06          | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ X0)
% 0.89/1.06          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06          | (m1_subset_1 @ (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ X0 @ sk_A) @ 
% 0.89/1.06             (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['287', '288'])).
% 0.89/1.06  thf('290', plain, ((v5_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('291', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ X0)
% 0.89/1.06          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06          | (m1_subset_1 @ (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ X0 @ sk_A) @ 
% 0.89/1.06             (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('demod', [status(thm)], ['289', '290'])).
% 0.89/1.06  thf('292', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         (~ (l1_waybel_9 @ sk_A)
% 0.89/1.06          | (m1_subset_1 @ (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ X0 @ sk_A) @ 
% 0.89/1.06             (u1_struct_0 @ sk_A))
% 0.89/1.06          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ X0)
% 0.89/1.06          | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['286', '291'])).
% 0.89/1.06  thf('293', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('294', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((m1_subset_1 @ (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ X0 @ sk_A) @ 
% 0.89/1.06           (u1_struct_0 @ sk_A))
% 0.89/1.06          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ X0)
% 0.89/1.06          | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('demod', [status(thm)], ['292', '293'])).
% 0.89/1.06  thf('295', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (m1_subset_1 @ 
% 0.89/1.06           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A) @ 
% 0.89/1.06           (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['285', '294'])).
% 0.89/1.06  thf('296', plain,
% 0.89/1.06      (((m1_subset_1 @ 
% 0.89/1.06         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06          sk_A) @ 
% 0.89/1.06         (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['295'])).
% 0.89/1.06  thf('297', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['76'])).
% 0.89/1.06  thf('298', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['80'])).
% 0.89/1.06  thf('299', plain,
% 0.89/1.06      (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.89/1.06      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.89/1.06  thf('300', plain,
% 0.89/1.06      (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.89/1.06      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.89/1.06  thf('301', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['76'])).
% 0.89/1.06  thf('302', plain,
% 0.89/1.06      (((r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r2_lattice3 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06           (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['283'])).
% 0.89/1.06  thf('303', plain,
% 0.89/1.06      (((m1_subset_1 @ 
% 0.89/1.06         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06          sk_A) @ 
% 0.89/1.06         (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['295'])).
% 0.89/1.06  thf('304', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['76'])).
% 0.89/1.06  thf('305', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['80'])).
% 0.89/1.06  thf('306', plain,
% 0.89/1.06      (((m1_subset_1 @ 
% 0.89/1.06         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06          sk_A) @ 
% 0.89/1.06         (u1_struct_0 @ sk_A))
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['295'])).
% 0.89/1.06  thf('307', plain,
% 0.89/1.06      (((r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r2_lattice3 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06           (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['283'])).
% 0.89/1.06  thf('308', plain,
% 0.89/1.06      (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.89/1.06      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.89/1.06  thf('309', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('simplify', [status(thm)], ['76'])).
% 0.89/1.06  thf('310', plain,
% 0.89/1.06      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.89/1.06         ((r2_lattice3 @ X6 @ X5 @ (sk_D @ X4 @ X5 @ X6))
% 0.89/1.06          | ~ (r2_lattice3 @ X6 @ X5 @ X4)
% 0.89/1.06          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X6))
% 0.89/1.06          | (r1_yellow_0 @ X6 @ X5)
% 0.89/1.06          | ~ (l1_orders_2 @ X6)
% 0.89/1.06          | ~ (v5_orders_2 @ X6))),
% 0.89/1.06      inference('cnf', [status(esa)], [t15_yellow_0])).
% 0.89/1.06  thf('311', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | ~ (v5_orders_2 @ sk_A)
% 0.89/1.06          | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ X0)
% 0.89/1.06          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06          | (r2_lattice3 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ X0 @ sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['309', '310'])).
% 0.89/1.06  thf('312', plain, ((v5_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('313', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | ~ (l1_orders_2 @ sk_A)
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ X0)
% 0.89/1.06          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06          | (r2_lattice3 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ X0 @ sk_A)))),
% 0.89/1.06      inference('demod', [status(thm)], ['311', '312'])).
% 0.89/1.06  thf('314', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         (~ (l1_waybel_9 @ sk_A)
% 0.89/1.06          | (r2_lattice3 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ X0 @ sk_A))
% 0.89/1.06          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ X0)
% 0.89/1.06          | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['308', '313'])).
% 0.89/1.06  thf('315', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('316', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((r2_lattice3 @ sk_A @ X0 @ 
% 0.89/1.06           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ X0 @ sk_A))
% 0.89/1.06          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ X0)
% 0.89/1.06          | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('demod', [status(thm)], ['314', '315'])).
% 0.89/1.06  thf('317', plain,
% 0.89/1.06      (((v2_struct_0 @ sk_A)
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_A)
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (r2_lattice3 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06            sk_A)))),
% 0.89/1.06      inference('sup-', [status(thm)], ['307', '316'])).
% 0.89/1.06  thf('318', plain,
% 0.89/1.06      (((r2_lattice3 @ sk_A @ 
% 0.89/1.06         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06          sk_A))
% 0.89/1.06        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_B)
% 0.89/1.06        | (v2_struct_0 @ sk_A))),
% 0.89/1.06      inference('simplify', [status(thm)], ['317'])).
% 0.89/1.06  thf('319', plain,
% 0.89/1.06      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.89/1.06         (~ (v2_pre_topc @ X17)
% 0.89/1.06          | ~ (v8_pre_topc @ X17)
% 0.89/1.06          | ~ (v3_orders_2 @ X17)
% 0.89/1.06          | ~ (v4_orders_2 @ X17)
% 0.89/1.06          | ~ (v5_orders_2 @ X17)
% 0.89/1.06          | ~ (v1_lattice3 @ X17)
% 0.89/1.06          | ~ (v2_lattice3 @ X17)
% 0.89/1.06          | ~ (v1_compts_1 @ X17)
% 0.89/1.06          | ~ (l1_waybel_9 @ X17)
% 0.89/1.06          | (m1_subset_1 @ (sk_E_1 @ X17) @ (u1_struct_0 @ X17))
% 0.89/1.06          | ~ (r3_waybel_9 @ X17 @ X16 @ X18)
% 0.89/1.06          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.89/1.06          | (r3_orders_2 @ X17 @ X18 @ X19)
% 0.89/1.06          | ~ (r2_lattice3 @ X17 @ 
% 0.89/1.06               (k2_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.89/1.06                (u1_waybel_0 @ X17 @ X16)) @ 
% 0.89/1.06               X19)
% 0.89/1.06          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.89/1.06          | ~ (l1_waybel_0 @ X16 @ X17)
% 0.89/1.06          | ~ (v7_waybel_0 @ X16)
% 0.89/1.06          | ~ (v4_orders_2 @ X16)
% 0.89/1.06          | (v2_struct_0 @ X16))),
% 0.89/1.06      inference('simplify', [status(thm)], ['151'])).
% 0.89/1.06  thf('320', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | ~ (v4_orders_2 @ sk_B)
% 0.89/1.06          | ~ (v7_waybel_0 @ sk_B)
% 0.89/1.06          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06              sk_A))
% 0.89/1.06          | ~ (m1_subset_1 @ 
% 0.89/1.06               (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06                sk_A) @ 
% 0.89/1.06               (u1_struct_0 @ sk_A))
% 0.89/1.06          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.06          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | ~ (l1_waybel_9 @ sk_A)
% 0.89/1.06          | ~ (v1_compts_1 @ sk_A)
% 0.89/1.06          | ~ (v2_lattice3 @ sk_A)
% 0.89/1.06          | ~ (v1_lattice3 @ sk_A)
% 0.89/1.06          | ~ (v5_orders_2 @ sk_A)
% 0.89/1.06          | ~ (v4_orders_2 @ sk_A)
% 0.89/1.06          | ~ (v3_orders_2 @ sk_A)
% 0.89/1.06          | ~ (v8_pre_topc @ sk_A)
% 0.89/1.06          | ~ (v2_pre_topc @ sk_A))),
% 0.89/1.06      inference('sup-', [status(thm)], ['318', '319'])).
% 0.89/1.06  thf('321', plain, ((v4_orders_2 @ sk_B)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('322', plain, ((v7_waybel_0 @ sk_B)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('323', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('324', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('325', plain, ((v1_compts_1 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('326', plain, ((v2_lattice3 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('327', plain, ((v1_lattice3 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('328', plain, ((v5_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('329', plain, ((v4_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('330', plain, ((v3_orders_2 @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('331', plain, ((v8_pre_topc @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('332', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.06  thf('333', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((v2_struct_0 @ sk_A)
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.06          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.06             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.06          | (v2_struct_0 @ sk_B)
% 0.89/1.06          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.06             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06              sk_A))
% 0.89/1.06          | ~ (m1_subset_1 @ 
% 0.89/1.06               (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.06                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.06                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.06                sk_A) @ 
% 0.89/1.06               (u1_struct_0 @ sk_A))
% 0.89/1.06          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.06          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.06      inference('demod', [status(thm)],
% 0.89/1.06                ['320', '321', '322', '323', '324', '325', '326', '327', 
% 0.89/1.06                 '328', '329', '330', '331', '332'])).
% 0.89/1.06  thf('334', plain,
% 0.89/1.06      (![X0 : $i]:
% 0.89/1.06         ((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.06          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.07          | ~ (m1_subset_1 @ 
% 0.89/1.07               (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07                sk_A) @ 
% 0.89/1.07               (u1_struct_0 @ sk_A))
% 0.89/1.07          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.07             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07              sk_A))
% 0.89/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.07          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07          | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07          | (v2_struct_0 @ sk_B)
% 0.89/1.07          | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['333'])).
% 0.89/1.07  thf('335', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ sk_A)
% 0.89/1.07          | (v2_struct_0 @ sk_B)
% 0.89/1.07          | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07          | (v2_struct_0 @ sk_A)
% 0.89/1.07          | (v2_struct_0 @ sk_B)
% 0.89/1.07          | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.07          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.07             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07              sk_A))
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.07          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['306', '334'])).
% 0.89/1.07  thf('336', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.07          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.07             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07              sk_A))
% 0.89/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.07          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07          | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07          | (v2_struct_0 @ sk_B)
% 0.89/1.07          | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['335'])).
% 0.89/1.07  thf('337', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07            sk_A))
% 0.89/1.07        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['305', '336'])).
% 0.89/1.07  thf('338', plain,
% 0.89/1.07      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07            sk_A))
% 0.89/1.07        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['337'])).
% 0.89/1.07  thf('339', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07            sk_A))
% 0.89/1.07        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['304', '338'])).
% 0.89/1.07  thf('340', plain,
% 0.89/1.07      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07            sk_A))
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['339'])).
% 0.89/1.07  thf('341', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ sk_A)
% 0.89/1.07          | ~ (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 0.89/1.07          | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 0.89/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('demod', [status(thm)], ['181', '182'])).
% 0.89/1.07  thf('342', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | ~ (m1_subset_1 @ 
% 0.89/1.07             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07              sk_A) @ 
% 0.89/1.07             (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07            sk_A))
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('sup-', [status(thm)], ['340', '341'])).
% 0.89/1.07  thf('343', plain,
% 0.89/1.07      (((r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07          sk_A))
% 0.89/1.07        | ~ (m1_subset_1 @ 
% 0.89/1.07             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07              sk_A) @ 
% 0.89/1.07             (u1_struct_0 @ sk_A))
% 0.89/1.07        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['342'])).
% 0.89/1.07  thf('344', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07            sk_A)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['303', '343'])).
% 0.89/1.07  thf('345', plain,
% 0.89/1.07      (((r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07          sk_A))
% 0.89/1.07        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['344'])).
% 0.89/1.07  thf('346', plain,
% 0.89/1.07      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.89/1.07         (~ (r1_orders_2 @ X6 @ X4 @ (sk_D @ X4 @ X5 @ X6))
% 0.89/1.07          | ~ (r2_lattice3 @ X6 @ X5 @ X4)
% 0.89/1.07          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X6))
% 0.89/1.07          | (r1_yellow_0 @ X6 @ X5)
% 0.89/1.07          | ~ (l1_orders_2 @ X6)
% 0.89/1.07          | ~ (v5_orders_2 @ X6))),
% 0.89/1.07      inference('cnf', [status(esa)], [t15_yellow_0])).
% 0.89/1.07  thf('347', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | ~ (v5_orders_2 @ sk_A)
% 0.89/1.07        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | ~ (r2_lattice3 @ sk_A @ 
% 0.89/1.07             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07             (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['345', '346'])).
% 0.89/1.07  thf('348', plain, ((v5_orders_2 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('349', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | ~ (r2_lattice3 @ sk_A @ 
% 0.89/1.07             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07             (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('demod', [status(thm)], ['347', '348'])).
% 0.89/1.07  thf('350', plain,
% 0.89/1.07      ((~ (r2_lattice3 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07           (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.07        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['349'])).
% 0.89/1.07  thf('351', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.07        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['302', '350'])).
% 0.89/1.07  thf('352', plain,
% 0.89/1.07      ((~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.07        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['351'])).
% 0.89/1.07  thf('353', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | ~ (l1_orders_2 @ sk_A))),
% 0.89/1.07      inference('sup-', [status(thm)], ['301', '352'])).
% 0.89/1.07  thf('354', plain,
% 0.89/1.07      ((~ (l1_orders_2 @ sk_A)
% 0.89/1.07        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['353'])).
% 0.89/1.07  thf('355', plain,
% 0.89/1.07      ((~ (l1_waybel_9 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['300', '354'])).
% 0.89/1.07  thf('356', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('357', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('demod', [status(thm)], ['355', '356'])).
% 0.89/1.07  thf('358', plain,
% 0.89/1.07      (![X9 : $i, X10 : $i]:
% 0.89/1.07         (~ (l1_waybel_0 @ X9 @ X10)
% 0.89/1.07          | ~ (r1_yellow_0 @ X10 @ 
% 0.89/1.07               (k2_relset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X10) @ 
% 0.89/1.07                (u1_waybel_0 @ X10 @ X9)))
% 0.89/1.07          | (r1_waybel_9 @ X10 @ X9)
% 0.89/1.07          | ~ (l1_orders_2 @ X10))),
% 0.89/1.07      inference('cnf', [status(esa)], [d3_waybel_9])).
% 0.89/1.07  thf('359', plain,
% 0.89/1.07      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.89/1.07      inference('sup-', [status(thm)], ['357', '358'])).
% 0.89/1.07  thf('360', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('361', plain,
% 0.89/1.07      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B))),
% 0.89/1.07      inference('demod', [status(thm)], ['359', '360'])).
% 0.89/1.07  thf('362', plain,
% 0.89/1.07      ((~ (l1_orders_2 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('simplify', [status(thm)], ['361'])).
% 0.89/1.07  thf('363', plain,
% 0.89/1.07      ((~ (l1_waybel_9 @ sk_A)
% 0.89/1.07        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('sup-', [status(thm)], ['299', '362'])).
% 0.89/1.07  thf('364', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('365', plain,
% 0.89/1.07      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('demod', [status(thm)], ['363', '364'])).
% 0.89/1.07  thf('366', plain,
% 0.89/1.07      (![X29 : $i]:
% 0.89/1.07         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X29) @ sk_A @ sk_A)
% 0.89/1.07          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('367', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A))),
% 0.89/1.07      inference('sup-', [status(thm)], ['365', '366'])).
% 0.89/1.07  thf('368', plain,
% 0.89/1.07      (((m1_subset_1 @ 
% 0.89/1.07         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07          sk_A) @ 
% 0.89/1.07         (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['295'])).
% 0.89/1.07  thf('369', plain,
% 0.89/1.07      (((r2_lattice3 @ sk_A @ 
% 0.89/1.07         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07          sk_A))
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['317'])).
% 0.89/1.07  thf('370', plain,
% 0.89/1.07      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.89/1.07         (~ (v2_pre_topc @ X17)
% 0.89/1.07          | ~ (v8_pre_topc @ X17)
% 0.89/1.07          | ~ (v3_orders_2 @ X17)
% 0.89/1.07          | ~ (v4_orders_2 @ X17)
% 0.89/1.07          | ~ (v5_orders_2 @ X17)
% 0.89/1.07          | ~ (v1_lattice3 @ X17)
% 0.89/1.07          | ~ (v2_lattice3 @ X17)
% 0.89/1.07          | ~ (v1_compts_1 @ X17)
% 0.89/1.07          | ~ (l1_waybel_9 @ X17)
% 0.89/1.07          | ~ (v5_pre_topc @ (k4_waybel_1 @ X17 @ (sk_E_1 @ X17)) @ X17 @ X17)
% 0.89/1.07          | ~ (r3_waybel_9 @ X17 @ X16 @ X18)
% 0.89/1.07          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.89/1.07          | (r3_orders_2 @ X17 @ X18 @ X19)
% 0.89/1.07          | ~ (r2_lattice3 @ X17 @ 
% 0.89/1.07               (k2_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.89/1.07                (u1_waybel_0 @ X17 @ X16)) @ 
% 0.89/1.07               X19)
% 0.89/1.07          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.89/1.07          | ~ (l1_waybel_0 @ X16 @ X17)
% 0.89/1.07          | ~ (v7_waybel_0 @ X16)
% 0.89/1.07          | ~ (v4_orders_2 @ X16)
% 0.89/1.07          | (v2_struct_0 @ X16))),
% 0.89/1.07      inference('simplify', [status(thm)], ['211'])).
% 0.89/1.07  thf('371', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ sk_A)
% 0.89/1.07          | (v2_struct_0 @ sk_B)
% 0.89/1.07          | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07          | (v2_struct_0 @ sk_B)
% 0.89/1.07          | ~ (v4_orders_2 @ sk_B)
% 0.89/1.07          | ~ (v7_waybel_0 @ sk_B)
% 0.89/1.07          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.89/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.07          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.07             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07              sk_A))
% 0.89/1.07          | ~ (m1_subset_1 @ 
% 0.89/1.07               (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07                sk_A) @ 
% 0.89/1.07               (u1_struct_0 @ sk_A))
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.07          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 0.89/1.07               sk_A)
% 0.89/1.07          | ~ (l1_waybel_9 @ sk_A)
% 0.89/1.07          | ~ (v1_compts_1 @ sk_A)
% 0.89/1.07          | ~ (v2_lattice3 @ sk_A)
% 0.89/1.07          | ~ (v1_lattice3 @ sk_A)
% 0.89/1.07          | ~ (v5_orders_2 @ sk_A)
% 0.89/1.07          | ~ (v4_orders_2 @ sk_A)
% 0.89/1.07          | ~ (v3_orders_2 @ sk_A)
% 0.89/1.07          | ~ (v8_pre_topc @ sk_A)
% 0.89/1.07          | ~ (v2_pre_topc @ sk_A))),
% 0.89/1.07      inference('sup-', [status(thm)], ['369', '370'])).
% 0.89/1.07  thf('372', plain, ((v4_orders_2 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('373', plain, ((v7_waybel_0 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('374', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('375', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('376', plain, ((v1_compts_1 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('377', plain, ((v2_lattice3 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('378', plain, ((v1_lattice3 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('379', plain, ((v5_orders_2 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('380', plain, ((v4_orders_2 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('381', plain, ((v3_orders_2 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('382', plain, ((v8_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('383', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('384', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ sk_A)
% 0.89/1.07          | (v2_struct_0 @ sk_B)
% 0.89/1.07          | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07          | (v2_struct_0 @ sk_B)
% 0.89/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.07          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.07             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07              sk_A))
% 0.89/1.07          | ~ (m1_subset_1 @ 
% 0.89/1.07               (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07                sk_A) @ 
% 0.89/1.07               (u1_struct_0 @ sk_A))
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.07          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 0.89/1.07               sk_A))),
% 0.89/1.07      inference('demod', [status(thm)],
% 0.89/1.07                ['371', '372', '373', '374', '375', '376', '377', '378', 
% 0.89/1.07                 '379', '380', '381', '382', '383'])).
% 0.89/1.07  thf('385', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.07          | ~ (m1_subset_1 @ 
% 0.89/1.07               (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07                sk_A) @ 
% 0.89/1.07               (u1_struct_0 @ sk_A))
% 0.89/1.07          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.07             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07              sk_A))
% 0.89/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.07          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07          | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07          | (v2_struct_0 @ sk_B)
% 0.89/1.07          | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['384'])).
% 0.89/1.07  thf('386', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ sk_A)
% 0.89/1.07          | (v2_struct_0 @ sk_B)
% 0.89/1.07          | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07          | (v2_struct_0 @ sk_A)
% 0.89/1.07          | (v2_struct_0 @ sk_B)
% 0.89/1.07          | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.07          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.07             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07              sk_A))
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.07          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 0.89/1.07               sk_A))),
% 0.89/1.07      inference('sup-', [status(thm)], ['368', '385'])).
% 0.89/1.07  thf('387', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.07          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.07             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07              sk_A))
% 0.89/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.07          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07          | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07          | (v2_struct_0 @ sk_B)
% 0.89/1.07          | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['386'])).
% 0.89/1.07  thf('388', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07          | (v2_struct_0 @ sk_B)
% 0.89/1.07          | (v2_struct_0 @ sk_A)
% 0.89/1.07          | (v2_struct_0 @ sk_A)
% 0.89/1.07          | (v2_struct_0 @ sk_B)
% 0.89/1.07          | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.07          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.07             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07              sk_A))
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0))),
% 0.89/1.07      inference('sup-', [status(thm)], ['367', '387'])).
% 0.89/1.07  thf('389', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.89/1.07          | (r3_orders_2 @ sk_A @ X0 @ 
% 0.89/1.07             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07              sk_A))
% 0.89/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.89/1.07          | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07          | (v2_struct_0 @ sk_A)
% 0.89/1.07          | (v2_struct_0 @ sk_B)
% 0.89/1.07          | (r1_waybel_9 @ sk_A @ sk_B))),
% 0.89/1.07      inference('simplify', [status(thm)], ['388'])).
% 0.89/1.07  thf('390', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07            sk_A)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['298', '389'])).
% 0.89/1.07  thf('391', plain,
% 0.89/1.07      (((r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07          sk_A))
% 0.89/1.07        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['390'])).
% 0.89/1.07  thf('392', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07            sk_A)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['297', '391'])).
% 0.89/1.07  thf('393', plain,
% 0.89/1.07      (((r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07          sk_A))
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['392'])).
% 0.89/1.07  thf('394', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ sk_A)
% 0.89/1.07          | ~ (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 0.89/1.07          | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 0.89/1.07          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('demod', [status(thm)], ['181', '182'])).
% 0.89/1.07  thf('395', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | ~ (m1_subset_1 @ 
% 0.89/1.07             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07              sk_A) @ 
% 0.89/1.07             (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07            sk_A))
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('sup-', [status(thm)], ['393', '394'])).
% 0.89/1.07  thf('396', plain,
% 0.89/1.07      (((r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07          sk_A))
% 0.89/1.07        | ~ (m1_subset_1 @ 
% 0.89/1.07             (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07              sk_A) @ 
% 0.89/1.07             (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['395'])).
% 0.89/1.07  thf('397', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07            sk_A)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['296', '396'])).
% 0.89/1.07  thf('398', plain,
% 0.89/1.07      (((r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07         (sk_D @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07          sk_A))
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['397'])).
% 0.89/1.07  thf('399', plain,
% 0.89/1.07      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.89/1.07         (~ (r1_orders_2 @ X6 @ X4 @ (sk_D @ X4 @ X5 @ X6))
% 0.89/1.07          | ~ (r2_lattice3 @ X6 @ X5 @ X4)
% 0.89/1.07          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X6))
% 0.89/1.07          | (r1_yellow_0 @ X6 @ X5)
% 0.89/1.07          | ~ (l1_orders_2 @ X6)
% 0.89/1.07          | ~ (v5_orders_2 @ X6))),
% 0.89/1.07      inference('cnf', [status(esa)], [t15_yellow_0])).
% 0.89/1.07  thf('400', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | ~ (v5_orders_2 @ sk_A)
% 0.89/1.07        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | ~ (r2_lattice3 @ sk_A @ 
% 0.89/1.07             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07             (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['398', '399'])).
% 0.89/1.07  thf('401', plain, ((v5_orders_2 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('402', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | ~ (r2_lattice3 @ sk_A @ 
% 0.89/1.07             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07             (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('demod', [status(thm)], ['400', '401'])).
% 0.89/1.07  thf('403', plain,
% 0.89/1.07      ((~ (r2_lattice3 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.89/1.07           (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['402'])).
% 0.89/1.07  thf('404', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.07        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['284', '403'])).
% 0.89/1.07  thf('405', plain,
% 0.89/1.07      ((~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['404'])).
% 0.89/1.07  thf('406', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | ~ (l1_orders_2 @ sk_A))),
% 0.89/1.07      inference('sup-', [status(thm)], ['77', '405'])).
% 0.89/1.07  thf('407', plain,
% 0.89/1.07      ((~ (l1_orders_2 @ sk_A)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['406'])).
% 0.89/1.07  thf('408', plain,
% 0.89/1.07      ((~ (l1_waybel_9 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['2', '407'])).
% 0.89/1.07  thf('409', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('410', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (r1_yellow_0 @ sk_A @ 
% 0.89/1.07           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.07            (u1_waybel_0 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('demod', [status(thm)], ['408', '409'])).
% 0.89/1.07  thf('411', plain,
% 0.89/1.07      (![X9 : $i, X10 : $i]:
% 0.89/1.07         (~ (l1_waybel_0 @ X9 @ X10)
% 0.89/1.07          | ~ (r1_yellow_0 @ X10 @ 
% 0.89/1.07               (k2_relset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X10) @ 
% 0.89/1.07                (u1_waybel_0 @ X10 @ X9)))
% 0.89/1.07          | (r1_waybel_9 @ X10 @ X9)
% 0.89/1.07          | ~ (l1_orders_2 @ X10))),
% 0.89/1.07      inference('cnf', [status(esa)], [d3_waybel_9])).
% 0.89/1.07  thf('412', plain,
% 0.89/1.07      (((r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.89/1.07      inference('sup-', [status(thm)], ['410', '411'])).
% 0.89/1.07  thf('413', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('414', plain,
% 0.89/1.07      (((r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | ~ (l1_orders_2 @ sk_A)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B))),
% 0.89/1.07      inference('demod', [status(thm)], ['412', '413'])).
% 0.89/1.07  thf('415', plain,
% 0.89/1.07      ((~ (l1_orders_2 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B))),
% 0.89/1.07      inference('simplify', [status(thm)], ['414'])).
% 0.89/1.07  thf('416', plain,
% 0.89/1.07      ((~ (l1_waybel_9 @ sk_A)
% 0.89/1.07        | (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('sup-', [status(thm)], ['1', '415'])).
% 0.89/1.07  thf('417', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('418', plain,
% 0.89/1.07      (((r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('demod', [status(thm)], ['416', '417'])).
% 0.89/1.07  thf('419', plain,
% 0.89/1.07      ((~ (r1_waybel_9 @ sk_A @ sk_B)
% 0.89/1.07        | ~ (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07             (k10_yellow_6 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('420', plain,
% 0.89/1.07      ((~ (r1_waybel_9 @ sk_A @ sk_B)) <= (~ ((r1_waybel_9 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('split', [status(esa)], ['419'])).
% 0.89/1.07  thf('421', plain,
% 0.89/1.07      (![X11 : $i]: ((l1_orders_2 @ X11) | ~ (l1_waybel_9 @ X11))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.89/1.07  thf('422', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('clc', [status(thm)], ['72', '73'])).
% 0.89/1.07  thf('423', plain,
% 0.89/1.07      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('clc', [status(thm)], ['14', '15'])).
% 0.89/1.07  thf('424', plain,
% 0.89/1.07      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('clc', [status(thm)], ['26', '27'])).
% 0.89/1.07  thf(t33_waybel_9, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.89/1.07         ( v8_pre_topc @ A ) & ( v1_compts_1 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.07       ( ![B:$i]:
% 0.89/1.07         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.89/1.07             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.89/1.07           ( ( ![C:$i]:
% 0.89/1.07               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.89/1.07                 ( ![D:$i]:
% 0.89/1.07                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.89/1.07                     ( ( ( r3_waybel_9 @ A @ B @ C ) & 
% 0.89/1.07                         ( r3_waybel_9 @ A @ B @ D ) ) =>
% 0.89/1.07                       ( ( C ) = ( D ) ) ) ) ) ) ) =>
% 0.89/1.07             ( ![C:$i]:
% 0.89/1.07               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.89/1.07                 ( ( r3_waybel_9 @ A @ B @ C ) =>
% 0.89/1.07                   ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.89/1.07  thf('425', plain,
% 0.89/1.07      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.89/1.07         ((v2_struct_0 @ X23)
% 0.89/1.07          | ~ (v4_orders_2 @ X23)
% 0.89/1.07          | ~ (v7_waybel_0 @ X23)
% 0.89/1.07          | ~ (l1_waybel_0 @ X23 @ X24)
% 0.89/1.07          | ~ (r3_waybel_9 @ X24 @ X23 @ X25)
% 0.89/1.07          | (r2_hidden @ X25 @ (k10_yellow_6 @ X24 @ X23))
% 0.89/1.07          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.89/1.07          | (r3_waybel_9 @ X24 @ X23 @ (sk_C_2 @ X23 @ X24))
% 0.89/1.07          | ~ (l1_pre_topc @ X24)
% 0.89/1.07          | ~ (v1_compts_1 @ X24)
% 0.89/1.07          | ~ (v8_pre_topc @ X24)
% 0.89/1.07          | ~ (v2_pre_topc @ X24)
% 0.89/1.07          | (v2_struct_0 @ X24))),
% 0.89/1.07      inference('cnf', [status(esa)], [t33_waybel_9])).
% 0.89/1.07  thf('426', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ sk_A)
% 0.89/1.07          | (v2_struct_0 @ sk_A)
% 0.89/1.07          | ~ (v2_pre_topc @ sk_A)
% 0.89/1.07          | ~ (v8_pre_topc @ sk_A)
% 0.89/1.07          | ~ (v1_compts_1 @ sk_A)
% 0.89/1.07          | ~ (l1_pre_topc @ sk_A)
% 0.89/1.07          | (r3_waybel_9 @ sk_A @ X0 @ (sk_C_2 @ X0 @ sk_A))
% 0.89/1.07          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.07          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07          | ~ (v7_waybel_0 @ X0)
% 0.89/1.07          | ~ (v4_orders_2 @ X0)
% 0.89/1.07          | (v2_struct_0 @ X0))),
% 0.89/1.07      inference('sup-', [status(thm)], ['424', '425'])).
% 0.89/1.07  thf('427', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('428', plain, ((v8_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('429', plain, ((v1_compts_1 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('430', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.07      inference('sup-', [status(thm)], ['9', '10'])).
% 0.89/1.07  thf('431', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ sk_A)
% 0.89/1.07          | (v2_struct_0 @ sk_A)
% 0.89/1.07          | (r3_waybel_9 @ sk_A @ X0 @ (sk_C_2 @ X0 @ sk_A))
% 0.89/1.07          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.07          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07          | ~ (v7_waybel_0 @ X0)
% 0.89/1.07          | ~ (v4_orders_2 @ X0)
% 0.89/1.07          | (v2_struct_0 @ X0))),
% 0.89/1.07      inference('demod', [status(thm)], ['426', '427', '428', '429', '430'])).
% 0.89/1.07  thf('432', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ X0)
% 0.89/1.07          | ~ (v4_orders_2 @ X0)
% 0.89/1.07          | ~ (v7_waybel_0 @ X0)
% 0.89/1.07          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.07          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.89/1.07          | (r3_waybel_9 @ sk_A @ X0 @ (sk_C_2 @ X0 @ sk_A))
% 0.89/1.07          | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['431'])).
% 0.89/1.07  thf('433', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_2 @ sk_B @ sk_A))
% 0.89/1.07        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.89/1.07        | ~ (v7_waybel_0 @ sk_B)
% 0.89/1.07        | ~ (v4_orders_2 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B))),
% 0.89/1.07      inference('sup-', [status(thm)], ['423', '432'])).
% 0.89/1.07  thf('434', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('435', plain, ((v7_waybel_0 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('436', plain, ((v4_orders_2 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('437', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_2 @ sk_B @ sk_A))
% 0.89/1.07        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07        | (v2_struct_0 @ sk_B))),
% 0.89/1.07      inference('demod', [status(thm)], ['433', '434', '435', '436'])).
% 0.89/1.07  thf('438', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_B)
% 0.89/1.07        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_2 @ sk_B @ sk_A))
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['437'])).
% 0.89/1.07  thf('439', plain,
% 0.89/1.07      (((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_2 @ sk_B @ sk_A))
% 0.89/1.07        | (v2_struct_0 @ sk_B))),
% 0.89/1.07      inference('sup+', [status(thm)], ['422', '438'])).
% 0.89/1.07  thf('440', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_B)
% 0.89/1.07        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_2 @ sk_B @ sk_A))
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (k10_yellow_6 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('simplify', [status(thm)], ['439'])).
% 0.89/1.07  thf('441', plain,
% 0.89/1.07      ((~ (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (k10_yellow_6 @ sk_A @ sk_B)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('split', [status(esa)], ['419'])).
% 0.89/1.07  thf('442', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_A)
% 0.89/1.07         | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_2 @ sk_B @ sk_A))
% 0.89/1.07         | (v2_struct_0 @ sk_B)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['440', '441'])).
% 0.89/1.07  thf('443', plain, (~ (v2_struct_0 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('444', plain,
% 0.89/1.07      ((((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_2 @ sk_B @ sk_A))
% 0.89/1.07         | (v2_struct_0 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('clc', [status(thm)], ['442', '443'])).
% 0.89/1.07  thf('445', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('clc', [status(thm)], ['72', '73'])).
% 0.89/1.07  thf('446', plain,
% 0.89/1.07      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('clc', [status(thm)], ['14', '15'])).
% 0.89/1.07  thf('447', plain,
% 0.89/1.07      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('clc', [status(thm)], ['26', '27'])).
% 0.89/1.07  thf('448', plain,
% 0.89/1.07      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.89/1.07         ((v2_struct_0 @ X23)
% 0.89/1.07          | ~ (v4_orders_2 @ X23)
% 0.89/1.07          | ~ (v7_waybel_0 @ X23)
% 0.89/1.07          | ~ (l1_waybel_0 @ X23 @ X24)
% 0.89/1.07          | ~ (r3_waybel_9 @ X24 @ X23 @ X25)
% 0.89/1.07          | (r2_hidden @ X25 @ (k10_yellow_6 @ X24 @ X23))
% 0.89/1.07          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.89/1.07          | (m1_subset_1 @ (sk_C_2 @ X23 @ X24) @ (u1_struct_0 @ X24))
% 0.89/1.07          | ~ (l1_pre_topc @ X24)
% 0.89/1.07          | ~ (v1_compts_1 @ X24)
% 0.89/1.07          | ~ (v8_pre_topc @ X24)
% 0.89/1.07          | ~ (v2_pre_topc @ X24)
% 0.89/1.07          | (v2_struct_0 @ X24))),
% 0.89/1.07      inference('cnf', [status(esa)], [t33_waybel_9])).
% 0.89/1.07  thf('449', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ sk_A)
% 0.89/1.07          | (v2_struct_0 @ sk_A)
% 0.89/1.07          | ~ (v2_pre_topc @ sk_A)
% 0.89/1.07          | ~ (v8_pre_topc @ sk_A)
% 0.89/1.07          | ~ (v1_compts_1 @ sk_A)
% 0.89/1.07          | ~ (l1_pre_topc @ sk_A)
% 0.89/1.07          | (m1_subset_1 @ (sk_C_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.07          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07          | ~ (v7_waybel_0 @ X0)
% 0.89/1.07          | ~ (v4_orders_2 @ X0)
% 0.89/1.07          | (v2_struct_0 @ X0))),
% 0.89/1.07      inference('sup-', [status(thm)], ['447', '448'])).
% 0.89/1.07  thf('450', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('451', plain, ((v8_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('452', plain, ((v1_compts_1 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('453', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.07      inference('sup-', [status(thm)], ['9', '10'])).
% 0.89/1.07  thf('454', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ sk_A)
% 0.89/1.07          | (v2_struct_0 @ sk_A)
% 0.89/1.07          | (m1_subset_1 @ (sk_C_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.07          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07          | ~ (v7_waybel_0 @ X0)
% 0.89/1.07          | ~ (v4_orders_2 @ X0)
% 0.89/1.07          | (v2_struct_0 @ X0))),
% 0.89/1.07      inference('demod', [status(thm)], ['449', '450', '451', '452', '453'])).
% 0.89/1.07  thf('455', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ X0)
% 0.89/1.07          | ~ (v4_orders_2 @ X0)
% 0.89/1.07          | ~ (v7_waybel_0 @ X0)
% 0.89/1.07          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.07          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.89/1.07          | (m1_subset_1 @ (sk_C_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07          | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['454'])).
% 0.89/1.07  thf('456', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.89/1.07        | ~ (v7_waybel_0 @ sk_B)
% 0.89/1.07        | ~ (v4_orders_2 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B))),
% 0.89/1.07      inference('sup-', [status(thm)], ['446', '455'])).
% 0.89/1.07  thf('457', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('458', plain, ((v7_waybel_0 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('459', plain, ((v4_orders_2 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('460', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07        | (v2_struct_0 @ sk_B))),
% 0.89/1.07      inference('demod', [status(thm)], ['456', '457', '458', '459'])).
% 0.89/1.07  thf('461', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_B)
% 0.89/1.07        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07        | (m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['460'])).
% 0.89/1.07  thf('462', plain,
% 0.89/1.07      (((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (v2_struct_0 @ sk_B))),
% 0.89/1.07      inference('sup+', [status(thm)], ['445', '461'])).
% 0.89/1.07  thf('463', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_B)
% 0.89/1.07        | (m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (k10_yellow_6 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('simplify', [status(thm)], ['462'])).
% 0.89/1.07  thf('464', plain,
% 0.89/1.07      ((~ (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (k10_yellow_6 @ sk_A @ sk_B)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('split', [status(esa)], ['419'])).
% 0.89/1.07  thf('465', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_A)
% 0.89/1.07         | (m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07         | (v2_struct_0 @ sk_B)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['463', '464'])).
% 0.89/1.07  thf('466', plain, (~ (v2_struct_0 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('467', plain,
% 0.89/1.07      ((((m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07         | (v2_struct_0 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('clc', [status(thm)], ['465', '466'])).
% 0.89/1.07  thf('468', plain,
% 0.89/1.07      ((((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_2 @ sk_B @ sk_A))
% 0.89/1.07         | (v2_struct_0 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('clc', [status(thm)], ['442', '443'])).
% 0.89/1.07  thf('469', plain,
% 0.89/1.07      ((((m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07         | (v2_struct_0 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('clc', [status(thm)], ['465', '466'])).
% 0.89/1.07  thf('470', plain,
% 0.89/1.07      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.89/1.07         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.89/1.07          | (m1_subset_1 @ (sk_D_2 @ X27) @ (u1_struct_0 @ X27))
% 0.89/1.07          | ~ (v10_waybel_0 @ X28 @ X27)
% 0.89/1.07          | ~ (r3_waybel_9 @ X27 @ X28 @ X26)
% 0.89/1.07          | ((X26) = (k1_waybel_2 @ X27 @ X28))
% 0.89/1.07          | ~ (l1_waybel_0 @ X28 @ X27)
% 0.89/1.07          | ~ (v7_waybel_0 @ X28)
% 0.89/1.07          | ~ (v4_orders_2 @ X28)
% 0.89/1.07          | (v2_struct_0 @ X28)
% 0.89/1.07          | ~ (l1_waybel_9 @ X27)
% 0.89/1.07          | ~ (v1_compts_1 @ X27)
% 0.89/1.07          | ~ (v2_lattice3 @ X27)
% 0.89/1.07          | ~ (v1_lattice3 @ X27)
% 0.89/1.07          | ~ (v5_orders_2 @ X27)
% 0.89/1.07          | ~ (v4_orders_2 @ X27)
% 0.89/1.07          | ~ (v3_orders_2 @ X27)
% 0.89/1.07          | ~ (v8_pre_topc @ X27)
% 0.89/1.07          | ~ (v2_pre_topc @ X27))),
% 0.89/1.07      inference('cnf', [status(esa)], [t35_waybel_9])).
% 0.89/1.07  thf('471', plain,
% 0.89/1.07      ((![X0 : $i]:
% 0.89/1.07          ((v2_struct_0 @ sk_A)
% 0.89/1.07           | ~ (v2_pre_topc @ sk_A)
% 0.89/1.07           | ~ (v8_pre_topc @ sk_A)
% 0.89/1.07           | ~ (v3_orders_2 @ sk_A)
% 0.89/1.07           | ~ (v4_orders_2 @ sk_A)
% 0.89/1.07           | ~ (v5_orders_2 @ sk_A)
% 0.89/1.07           | ~ (v1_lattice3 @ sk_A)
% 0.89/1.07           | ~ (v2_lattice3 @ sk_A)
% 0.89/1.07           | ~ (v1_compts_1 @ sk_A)
% 0.89/1.07           | ~ (l1_waybel_9 @ sk_A)
% 0.89/1.07           | (v2_struct_0 @ X0)
% 0.89/1.07           | ~ (v4_orders_2 @ X0)
% 0.89/1.07           | ~ (v7_waybel_0 @ X0)
% 0.89/1.07           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 0.89/1.07           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_2 @ sk_B @ sk_A))
% 0.89/1.07           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['469', '470'])).
% 0.89/1.07  thf('472', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('473', plain, ((v8_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('474', plain, ((v3_orders_2 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('475', plain, ((v4_orders_2 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('476', plain, ((v5_orders_2 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('477', plain, ((v1_lattice3 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('478', plain, ((v2_lattice3 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('479', plain, ((v1_compts_1 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('480', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('481', plain,
% 0.89/1.07      ((![X0 : $i]:
% 0.89/1.07          ((v2_struct_0 @ sk_A)
% 0.89/1.07           | (v2_struct_0 @ X0)
% 0.89/1.07           | ~ (v4_orders_2 @ X0)
% 0.89/1.07           | ~ (v7_waybel_0 @ X0)
% 0.89/1.07           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 0.89/1.07           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_2 @ sk_B @ sk_A))
% 0.89/1.07           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('demod', [status(thm)],
% 0.89/1.07                ['471', '472', '473', '474', '475', '476', '477', '478', 
% 0.89/1.07                 '479', '480'])).
% 0.89/1.07  thf('482', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_A)
% 0.89/1.07         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07         | ~ (v10_waybel_0 @ sk_B @ sk_A)
% 0.89/1.07         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.89/1.07         | ~ (v7_waybel_0 @ sk_B)
% 0.89/1.07         | ~ (v4_orders_2 @ sk_B)
% 0.89/1.07         | (v2_struct_0 @ sk_B)
% 0.89/1.07         | (v2_struct_0 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['468', '481'])).
% 0.89/1.07  thf('483', plain, ((v10_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('484', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('485', plain, ((v7_waybel_0 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('486', plain, ((v4_orders_2 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('487', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_A)
% 0.89/1.07         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | (v2_struct_0 @ sk_B)
% 0.89/1.07         | (v2_struct_0 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('demod', [status(thm)], ['482', '483', '484', '485', '486'])).
% 0.89/1.07  thf('488', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_B)
% 0.89/1.07         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07         | (v2_struct_0 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('simplify', [status(thm)], ['487'])).
% 0.89/1.07  thf('489', plain,
% 0.89/1.07      (![X29 : $i]:
% 0.89/1.07         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X29) @ sk_A @ sk_A)
% 0.89/1.07          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('490', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_A)
% 0.89/1.07         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | (v2_struct_0 @ sk_B)
% 0.89/1.07         | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_D_2 @ sk_A)) @ sk_A @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['488', '489'])).
% 0.89/1.07  thf('491', plain,
% 0.89/1.07      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.89/1.07         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.89/1.07          | ~ (v5_pre_topc @ (k4_waybel_1 @ X27 @ (sk_D_2 @ X27)) @ X27 @ X27)
% 0.89/1.07          | ~ (v10_waybel_0 @ X28 @ X27)
% 0.89/1.07          | ~ (r3_waybel_9 @ X27 @ X28 @ X26)
% 0.89/1.07          | ((X26) = (k1_waybel_2 @ X27 @ X28))
% 0.89/1.07          | ~ (l1_waybel_0 @ X28 @ X27)
% 0.89/1.07          | ~ (v7_waybel_0 @ X28)
% 0.89/1.07          | ~ (v4_orders_2 @ X28)
% 0.89/1.07          | (v2_struct_0 @ X28)
% 0.89/1.07          | ~ (l1_waybel_9 @ X27)
% 0.89/1.07          | ~ (v1_compts_1 @ X27)
% 0.89/1.07          | ~ (v2_lattice3 @ X27)
% 0.89/1.07          | ~ (v1_lattice3 @ X27)
% 0.89/1.07          | ~ (v5_orders_2 @ X27)
% 0.89/1.07          | ~ (v4_orders_2 @ X27)
% 0.89/1.07          | ~ (v3_orders_2 @ X27)
% 0.89/1.07          | ~ (v8_pre_topc @ X27)
% 0.89/1.07          | ~ (v2_pre_topc @ X27))),
% 0.89/1.07      inference('cnf', [status(esa)], [t35_waybel_9])).
% 0.89/1.07  thf('492', plain,
% 0.89/1.07      ((![X0 : $i, X1 : $i]:
% 0.89/1.07          ((v2_struct_0 @ sk_B)
% 0.89/1.07           | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07           | (v2_struct_0 @ sk_A)
% 0.89/1.07           | ~ (v2_pre_topc @ sk_A)
% 0.89/1.07           | ~ (v8_pre_topc @ sk_A)
% 0.89/1.07           | ~ (v3_orders_2 @ sk_A)
% 0.89/1.07           | ~ (v4_orders_2 @ sk_A)
% 0.89/1.07           | ~ (v5_orders_2 @ sk_A)
% 0.89/1.07           | ~ (v1_lattice3 @ sk_A)
% 0.89/1.07           | ~ (v2_lattice3 @ sk_A)
% 0.89/1.07           | ~ (v1_compts_1 @ sk_A)
% 0.89/1.07           | ~ (l1_waybel_9 @ sk_A)
% 0.89/1.07           | (v2_struct_0 @ X0)
% 0.89/1.07           | ~ (v4_orders_2 @ X0)
% 0.89/1.07           | ~ (v7_waybel_0 @ X0)
% 0.89/1.07           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | ((X1) = (k1_waybel_2 @ sk_A @ X0))
% 0.89/1.07           | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 0.89/1.07           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['490', '491'])).
% 0.89/1.07  thf('493', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('494', plain, ((v8_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('495', plain, ((v3_orders_2 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('496', plain, ((v4_orders_2 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('497', plain, ((v5_orders_2 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('498', plain, ((v1_lattice3 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('499', plain, ((v2_lattice3 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('500', plain, ((v1_compts_1 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('501', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('502', plain,
% 0.89/1.07      ((![X0 : $i, X1 : $i]:
% 0.89/1.07          ((v2_struct_0 @ sk_B)
% 0.89/1.07           | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07           | (v2_struct_0 @ sk_A)
% 0.89/1.07           | (v2_struct_0 @ X0)
% 0.89/1.07           | ~ (v4_orders_2 @ X0)
% 0.89/1.07           | ~ (v7_waybel_0 @ X0)
% 0.89/1.07           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | ((X1) = (k1_waybel_2 @ sk_A @ X0))
% 0.89/1.07           | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 0.89/1.07           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('demod', [status(thm)],
% 0.89/1.07                ['492', '493', '494', '495', '496', '497', '498', '499', 
% 0.89/1.07                 '500', '501'])).
% 0.89/1.07  thf('503', plain,
% 0.89/1.07      ((![X0 : $i]:
% 0.89/1.07          ((v2_struct_0 @ sk_A)
% 0.89/1.07           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_2 @ sk_B @ sk_A))
% 0.89/1.07           | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 0.89/1.07           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | ~ (v7_waybel_0 @ X0)
% 0.89/1.07           | ~ (v4_orders_2 @ X0)
% 0.89/1.07           | (v2_struct_0 @ X0)
% 0.89/1.07           | (v2_struct_0 @ sk_A)
% 0.89/1.07           | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07           | (v2_struct_0 @ sk_B)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['467', '502'])).
% 0.89/1.07  thf('504', plain,
% 0.89/1.07      ((![X0 : $i]:
% 0.89/1.07          ((v2_struct_0 @ sk_B)
% 0.89/1.07           | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07           | (v2_struct_0 @ X0)
% 0.89/1.07           | ~ (v4_orders_2 @ X0)
% 0.89/1.07           | ~ (v7_waybel_0 @ X0)
% 0.89/1.07           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 0.89/1.07           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_2 @ sk_B @ sk_A))
% 0.89/1.07           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | (v2_struct_0 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('simplify', [status(thm)], ['503'])).
% 0.89/1.07  thf('505', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_A)
% 0.89/1.07         | (v2_struct_0 @ sk_A)
% 0.89/1.07         | ~ (v10_waybel_0 @ sk_B @ sk_A)
% 0.89/1.07         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.89/1.07         | ~ (v7_waybel_0 @ sk_B)
% 0.89/1.07         | ~ (v4_orders_2 @ sk_B)
% 0.89/1.07         | (v2_struct_0 @ sk_B)
% 0.89/1.07         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | (v2_struct_0 @ sk_B)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['444', '504'])).
% 0.89/1.07  thf('506', plain, ((v10_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('507', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('508', plain, ((v7_waybel_0 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('509', plain, ((v4_orders_2 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('510', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_A)
% 0.89/1.07         | (v2_struct_0 @ sk_A)
% 0.89/1.07         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | (v2_struct_0 @ sk_B)
% 0.89/1.07         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | (v2_struct_0 @ sk_B)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('demod', [status(thm)], ['505', '506', '507', '508', '509'])).
% 0.89/1.07  thf('511', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_B)
% 0.89/1.07         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | (v2_struct_0 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('simplify', [status(thm)], ['510'])).
% 0.89/1.07  thf('512', plain, (~ (v2_struct_0 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('513', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_A)
% 0.89/1.07         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('clc', [status(thm)], ['511', '512'])).
% 0.89/1.07  thf('514', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('simplify', [status(thm)], ['80'])).
% 0.89/1.07  thf('515', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('simplify', [status(thm)], ['76'])).
% 0.89/1.07  thf('516', plain,
% 0.89/1.07      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.89/1.07         ((v2_struct_0 @ X23)
% 0.89/1.07          | ~ (v4_orders_2 @ X23)
% 0.89/1.07          | ~ (v7_waybel_0 @ X23)
% 0.89/1.07          | ~ (l1_waybel_0 @ X23 @ X24)
% 0.89/1.07          | ~ (r3_waybel_9 @ X24 @ X23 @ X25)
% 0.89/1.07          | (r2_hidden @ X25 @ (k10_yellow_6 @ X24 @ X23))
% 0.89/1.07          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.89/1.07          | (r3_waybel_9 @ X24 @ X23 @ (sk_D_1 @ X23 @ X24))
% 0.89/1.07          | ~ (l1_pre_topc @ X24)
% 0.89/1.07          | ~ (v1_compts_1 @ X24)
% 0.89/1.07          | ~ (v8_pre_topc @ X24)
% 0.89/1.07          | ~ (v2_pre_topc @ X24)
% 0.89/1.07          | (v2_struct_0 @ X24))),
% 0.89/1.07      inference('cnf', [status(esa)], [t33_waybel_9])).
% 0.89/1.07  thf('517', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ sk_A)
% 0.89/1.07          | (v2_struct_0 @ sk_A)
% 0.89/1.07          | ~ (v2_pre_topc @ sk_A)
% 0.89/1.07          | ~ (v8_pre_topc @ sk_A)
% 0.89/1.07          | ~ (v1_compts_1 @ sk_A)
% 0.89/1.07          | ~ (l1_pre_topc @ sk_A)
% 0.89/1.07          | (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ X0 @ sk_A))
% 0.89/1.07          | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07             (k10_yellow_6 @ sk_A @ X0))
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07          | ~ (v7_waybel_0 @ X0)
% 0.89/1.07          | ~ (v4_orders_2 @ X0)
% 0.89/1.07          | (v2_struct_0 @ X0))),
% 0.89/1.07      inference('sup-', [status(thm)], ['515', '516'])).
% 0.89/1.07  thf('518', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('519', plain, ((v8_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('520', plain, ((v1_compts_1 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('521', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.07      inference('sup-', [status(thm)], ['9', '10'])).
% 0.89/1.07  thf('522', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ sk_A)
% 0.89/1.07          | (v2_struct_0 @ sk_A)
% 0.89/1.07          | (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ X0 @ sk_A))
% 0.89/1.07          | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07             (k10_yellow_6 @ sk_A @ X0))
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07          | ~ (v7_waybel_0 @ X0)
% 0.89/1.07          | ~ (v4_orders_2 @ X0)
% 0.89/1.07          | (v2_struct_0 @ X0))),
% 0.89/1.07      inference('demod', [status(thm)], ['517', '518', '519', '520', '521'])).
% 0.89/1.07  thf('523', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ X0)
% 0.89/1.07          | ~ (v4_orders_2 @ X0)
% 0.89/1.07          | ~ (v7_waybel_0 @ X0)
% 0.89/1.07          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07          | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07             (k10_yellow_6 @ sk_A @ X0))
% 0.89/1.07          | (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ X0 @ sk_A))
% 0.89/1.07          | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['522'])).
% 0.89/1.07  thf('524', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 0.89/1.07        | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.89/1.07        | ~ (v7_waybel_0 @ sk_B)
% 0.89/1.07        | ~ (v4_orders_2 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B))),
% 0.89/1.07      inference('sup-', [status(thm)], ['514', '523'])).
% 0.89/1.07  thf('525', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('526', plain, ((v7_waybel_0 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('527', plain, ((v4_orders_2 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('528', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 0.89/1.07        | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07        | (v2_struct_0 @ sk_B))),
% 0.89/1.07      inference('demod', [status(thm)], ['524', '525', '526', '527'])).
% 0.89/1.07  thf('529', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_B)
% 0.89/1.07        | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['528'])).
% 0.89/1.07  thf('530', plain,
% 0.89/1.07      ((~ (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (k10_yellow_6 @ sk_A @ sk_B)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('split', [status(esa)], ['419'])).
% 0.89/1.07  thf('531', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_A)
% 0.89/1.07         | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 0.89/1.07         | (v2_struct_0 @ sk_B)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['529', '530'])).
% 0.89/1.07  thf('532', plain, (~ (v2_struct_0 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('533', plain,
% 0.89/1.07      ((((r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 0.89/1.07         | (v2_struct_0 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('clc', [status(thm)], ['531', '532'])).
% 0.89/1.07  thf('534', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('clc', [status(thm)], ['72', '73'])).
% 0.89/1.07  thf('535', plain,
% 0.89/1.07      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('clc', [status(thm)], ['14', '15'])).
% 0.89/1.07  thf('536', plain,
% 0.89/1.07      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('clc', [status(thm)], ['26', '27'])).
% 0.89/1.07  thf('537', plain,
% 0.89/1.07      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.89/1.07         ((v2_struct_0 @ X23)
% 0.89/1.07          | ~ (v4_orders_2 @ X23)
% 0.89/1.07          | ~ (v7_waybel_0 @ X23)
% 0.89/1.07          | ~ (l1_waybel_0 @ X23 @ X24)
% 0.89/1.07          | ~ (r3_waybel_9 @ X24 @ X23 @ X25)
% 0.89/1.07          | (r2_hidden @ X25 @ (k10_yellow_6 @ X24 @ X23))
% 0.89/1.07          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.89/1.07          | (m1_subset_1 @ (sk_D_1 @ X23 @ X24) @ (u1_struct_0 @ X24))
% 0.89/1.07          | ~ (l1_pre_topc @ X24)
% 0.89/1.07          | ~ (v1_compts_1 @ X24)
% 0.89/1.07          | ~ (v8_pre_topc @ X24)
% 0.89/1.07          | ~ (v2_pre_topc @ X24)
% 0.89/1.07          | (v2_struct_0 @ X24))),
% 0.89/1.07      inference('cnf', [status(esa)], [t33_waybel_9])).
% 0.89/1.07  thf('538', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ sk_A)
% 0.89/1.07          | (v2_struct_0 @ sk_A)
% 0.89/1.07          | ~ (v2_pre_topc @ sk_A)
% 0.89/1.07          | ~ (v8_pre_topc @ sk_A)
% 0.89/1.07          | ~ (v1_compts_1 @ sk_A)
% 0.89/1.07          | ~ (l1_pre_topc @ sk_A)
% 0.89/1.07          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.07          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07          | ~ (v7_waybel_0 @ X0)
% 0.89/1.07          | ~ (v4_orders_2 @ X0)
% 0.89/1.07          | (v2_struct_0 @ X0))),
% 0.89/1.07      inference('sup-', [status(thm)], ['536', '537'])).
% 0.89/1.07  thf('539', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('540', plain, ((v8_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('541', plain, ((v1_compts_1 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('542', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.07      inference('sup-', [status(thm)], ['9', '10'])).
% 0.89/1.07  thf('543', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ sk_A)
% 0.89/1.07          | (v2_struct_0 @ sk_A)
% 0.89/1.07          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.07          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07          | ~ (v7_waybel_0 @ X0)
% 0.89/1.07          | ~ (v4_orders_2 @ X0)
% 0.89/1.07          | (v2_struct_0 @ X0))),
% 0.89/1.07      inference('demod', [status(thm)], ['538', '539', '540', '541', '542'])).
% 0.89/1.07  thf('544', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ X0)
% 0.89/1.07          | ~ (v4_orders_2 @ X0)
% 0.89/1.07          | ~ (v7_waybel_0 @ X0)
% 0.89/1.07          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.89/1.07          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.89/1.07          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07          | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['543'])).
% 0.89/1.07  thf('545', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.89/1.07        | ~ (v7_waybel_0 @ sk_B)
% 0.89/1.07        | ~ (v4_orders_2 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B))),
% 0.89/1.07      inference('sup-', [status(thm)], ['535', '544'])).
% 0.89/1.07  thf('546', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('547', plain, ((v7_waybel_0 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('548', plain, ((v4_orders_2 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('549', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07        | (v2_struct_0 @ sk_B))),
% 0.89/1.07      inference('demod', [status(thm)], ['545', '546', '547', '548'])).
% 0.89/1.07  thf('550', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_B)
% 0.89/1.07        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['549'])).
% 0.89/1.07  thf('551', plain,
% 0.89/1.07      (((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (v2_struct_0 @ sk_B))),
% 0.89/1.07      inference('sup+', [status(thm)], ['534', '550'])).
% 0.89/1.07  thf('552', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_B)
% 0.89/1.07        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (k10_yellow_6 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('simplify', [status(thm)], ['551'])).
% 0.89/1.07  thf('553', plain,
% 0.89/1.07      ((~ (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (k10_yellow_6 @ sk_A @ sk_B)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('split', [status(esa)], ['419'])).
% 0.89/1.07  thf('554', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_A)
% 0.89/1.07         | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07         | (v2_struct_0 @ sk_B)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['552', '553'])).
% 0.89/1.07  thf('555', plain, (~ (v2_struct_0 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('556', plain,
% 0.89/1.07      ((((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07         | (v2_struct_0 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('clc', [status(thm)], ['554', '555'])).
% 0.89/1.07  thf('557', plain,
% 0.89/1.07      ((((r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 0.89/1.07         | (v2_struct_0 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('clc', [status(thm)], ['531', '532'])).
% 0.89/1.07  thf('558', plain,
% 0.89/1.07      ((((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07         | (v2_struct_0 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('clc', [status(thm)], ['554', '555'])).
% 0.89/1.07  thf('559', plain,
% 0.89/1.07      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.89/1.07         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.89/1.07          | (m1_subset_1 @ (sk_D_2 @ X27) @ (u1_struct_0 @ X27))
% 0.89/1.07          | ~ (v10_waybel_0 @ X28 @ X27)
% 0.89/1.07          | ~ (r3_waybel_9 @ X27 @ X28 @ X26)
% 0.89/1.07          | ((X26) = (k1_waybel_2 @ X27 @ X28))
% 0.89/1.07          | ~ (l1_waybel_0 @ X28 @ X27)
% 0.89/1.07          | ~ (v7_waybel_0 @ X28)
% 0.89/1.07          | ~ (v4_orders_2 @ X28)
% 0.89/1.07          | (v2_struct_0 @ X28)
% 0.89/1.07          | ~ (l1_waybel_9 @ X27)
% 0.89/1.07          | ~ (v1_compts_1 @ X27)
% 0.89/1.07          | ~ (v2_lattice3 @ X27)
% 0.89/1.07          | ~ (v1_lattice3 @ X27)
% 0.89/1.07          | ~ (v5_orders_2 @ X27)
% 0.89/1.07          | ~ (v4_orders_2 @ X27)
% 0.89/1.07          | ~ (v3_orders_2 @ X27)
% 0.89/1.07          | ~ (v8_pre_topc @ X27)
% 0.89/1.07          | ~ (v2_pre_topc @ X27))),
% 0.89/1.07      inference('cnf', [status(esa)], [t35_waybel_9])).
% 0.89/1.07  thf('560', plain,
% 0.89/1.07      ((![X0 : $i]:
% 0.89/1.07          ((v2_struct_0 @ sk_A)
% 0.89/1.07           | ~ (v2_pre_topc @ sk_A)
% 0.89/1.07           | ~ (v8_pre_topc @ sk_A)
% 0.89/1.07           | ~ (v3_orders_2 @ sk_A)
% 0.89/1.07           | ~ (v4_orders_2 @ sk_A)
% 0.89/1.07           | ~ (v5_orders_2 @ sk_A)
% 0.89/1.07           | ~ (v1_lattice3 @ sk_A)
% 0.89/1.07           | ~ (v2_lattice3 @ sk_A)
% 0.89/1.07           | ~ (v1_compts_1 @ sk_A)
% 0.89/1.07           | ~ (l1_waybel_9 @ sk_A)
% 0.89/1.07           | (v2_struct_0 @ X0)
% 0.89/1.07           | ~ (v4_orders_2 @ X0)
% 0.89/1.07           | ~ (v7_waybel_0 @ X0)
% 0.89/1.07           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 0.89/1.07           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_A))
% 0.89/1.07           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['558', '559'])).
% 0.89/1.07  thf('561', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('562', plain, ((v8_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('563', plain, ((v3_orders_2 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('564', plain, ((v4_orders_2 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('565', plain, ((v5_orders_2 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('566', plain, ((v1_lattice3 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('567', plain, ((v2_lattice3 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('568', plain, ((v1_compts_1 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('569', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('570', plain,
% 0.89/1.07      ((![X0 : $i]:
% 0.89/1.07          ((v2_struct_0 @ sk_A)
% 0.89/1.07           | (v2_struct_0 @ X0)
% 0.89/1.07           | ~ (v4_orders_2 @ X0)
% 0.89/1.07           | ~ (v7_waybel_0 @ X0)
% 0.89/1.07           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 0.89/1.07           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_A))
% 0.89/1.07           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('demod', [status(thm)],
% 0.89/1.07                ['560', '561', '562', '563', '564', '565', '566', '567', 
% 0.89/1.07                 '568', '569'])).
% 0.89/1.07  thf('571', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_A)
% 0.89/1.07         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07         | ~ (v10_waybel_0 @ sk_B @ sk_A)
% 0.89/1.07         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.89/1.07         | ~ (v7_waybel_0 @ sk_B)
% 0.89/1.07         | ~ (v4_orders_2 @ sk_B)
% 0.89/1.07         | (v2_struct_0 @ sk_B)
% 0.89/1.07         | (v2_struct_0 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['557', '570'])).
% 0.89/1.07  thf('572', plain, ((v10_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('573', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('574', plain, ((v7_waybel_0 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('575', plain, ((v4_orders_2 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('576', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_A)
% 0.89/1.07         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | (v2_struct_0 @ sk_B)
% 0.89/1.07         | (v2_struct_0 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('demod', [status(thm)], ['571', '572', '573', '574', '575'])).
% 0.89/1.07  thf('577', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_B)
% 0.89/1.07         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.89/1.07         | (v2_struct_0 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('simplify', [status(thm)], ['576'])).
% 0.89/1.07  thf('578', plain,
% 0.89/1.07      (![X29 : $i]:
% 0.89/1.07         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X29) @ sk_A @ sk_A)
% 0.89/1.07          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('579', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_A)
% 0.89/1.07         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | (v2_struct_0 @ sk_B)
% 0.89/1.07         | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_D_2 @ sk_A)) @ sk_A @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['577', '578'])).
% 0.89/1.07  thf('580', plain,
% 0.89/1.07      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.89/1.07         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.89/1.07          | ~ (v5_pre_topc @ (k4_waybel_1 @ X27 @ (sk_D_2 @ X27)) @ X27 @ X27)
% 0.89/1.07          | ~ (v10_waybel_0 @ X28 @ X27)
% 0.89/1.07          | ~ (r3_waybel_9 @ X27 @ X28 @ X26)
% 0.89/1.07          | ((X26) = (k1_waybel_2 @ X27 @ X28))
% 0.89/1.07          | ~ (l1_waybel_0 @ X28 @ X27)
% 0.89/1.07          | ~ (v7_waybel_0 @ X28)
% 0.89/1.07          | ~ (v4_orders_2 @ X28)
% 0.89/1.07          | (v2_struct_0 @ X28)
% 0.89/1.07          | ~ (l1_waybel_9 @ X27)
% 0.89/1.07          | ~ (v1_compts_1 @ X27)
% 0.89/1.07          | ~ (v2_lattice3 @ X27)
% 0.89/1.07          | ~ (v1_lattice3 @ X27)
% 0.89/1.07          | ~ (v5_orders_2 @ X27)
% 0.89/1.07          | ~ (v4_orders_2 @ X27)
% 0.89/1.07          | ~ (v3_orders_2 @ X27)
% 0.89/1.07          | ~ (v8_pre_topc @ X27)
% 0.89/1.07          | ~ (v2_pre_topc @ X27))),
% 0.89/1.07      inference('cnf', [status(esa)], [t35_waybel_9])).
% 0.89/1.07  thf('581', plain,
% 0.89/1.07      ((![X0 : $i, X1 : $i]:
% 0.89/1.07          ((v2_struct_0 @ sk_B)
% 0.89/1.07           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07           | (v2_struct_0 @ sk_A)
% 0.89/1.07           | ~ (v2_pre_topc @ sk_A)
% 0.89/1.07           | ~ (v8_pre_topc @ sk_A)
% 0.89/1.07           | ~ (v3_orders_2 @ sk_A)
% 0.89/1.07           | ~ (v4_orders_2 @ sk_A)
% 0.89/1.07           | ~ (v5_orders_2 @ sk_A)
% 0.89/1.07           | ~ (v1_lattice3 @ sk_A)
% 0.89/1.07           | ~ (v2_lattice3 @ sk_A)
% 0.89/1.07           | ~ (v1_compts_1 @ sk_A)
% 0.89/1.07           | ~ (l1_waybel_9 @ sk_A)
% 0.89/1.07           | (v2_struct_0 @ X0)
% 0.89/1.07           | ~ (v4_orders_2 @ X0)
% 0.89/1.07           | ~ (v7_waybel_0 @ X0)
% 0.89/1.07           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | ((X1) = (k1_waybel_2 @ sk_A @ X0))
% 0.89/1.07           | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 0.89/1.07           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['579', '580'])).
% 0.89/1.07  thf('582', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('583', plain, ((v8_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('584', plain, ((v3_orders_2 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('585', plain, ((v4_orders_2 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('586', plain, ((v5_orders_2 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('587', plain, ((v1_lattice3 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('588', plain, ((v2_lattice3 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('589', plain, ((v1_compts_1 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('590', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('591', plain,
% 0.89/1.07      ((![X0 : $i, X1 : $i]:
% 0.89/1.07          ((v2_struct_0 @ sk_B)
% 0.89/1.07           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07           | (v2_struct_0 @ sk_A)
% 0.89/1.07           | (v2_struct_0 @ X0)
% 0.89/1.07           | ~ (v4_orders_2 @ X0)
% 0.89/1.07           | ~ (v7_waybel_0 @ X0)
% 0.89/1.07           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | ((X1) = (k1_waybel_2 @ sk_A @ X0))
% 0.89/1.07           | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 0.89/1.07           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('demod', [status(thm)],
% 0.89/1.07                ['581', '582', '583', '584', '585', '586', '587', '588', 
% 0.89/1.07                 '589', '590'])).
% 0.89/1.07  thf('592', plain,
% 0.89/1.07      ((![X0 : $i]:
% 0.89/1.07          ((v2_struct_0 @ sk_A)
% 0.89/1.07           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_A))
% 0.89/1.07           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 0.89/1.07           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | ~ (v7_waybel_0 @ X0)
% 0.89/1.07           | ~ (v4_orders_2 @ X0)
% 0.89/1.07           | (v2_struct_0 @ X0)
% 0.89/1.07           | (v2_struct_0 @ sk_A)
% 0.89/1.07           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07           | (v2_struct_0 @ sk_B)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['556', '591'])).
% 0.89/1.07  thf('593', plain,
% 0.89/1.07      ((![X0 : $i]:
% 0.89/1.07          ((v2_struct_0 @ sk_B)
% 0.89/1.07           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07           | (v2_struct_0 @ X0)
% 0.89/1.07           | ~ (v4_orders_2 @ X0)
% 0.89/1.07           | ~ (v7_waybel_0 @ X0)
% 0.89/1.07           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 0.89/1.07           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_A))
% 0.89/1.07           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 0.89/1.07           | (v2_struct_0 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('simplify', [status(thm)], ['592'])).
% 0.89/1.07  thf('594', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_A)
% 0.89/1.07         | (v2_struct_0 @ sk_A)
% 0.89/1.07         | ~ (v10_waybel_0 @ sk_B @ sk_A)
% 0.89/1.07         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.89/1.07         | ~ (v7_waybel_0 @ sk_B)
% 0.89/1.07         | ~ (v4_orders_2 @ sk_B)
% 0.89/1.07         | (v2_struct_0 @ sk_B)
% 0.89/1.07         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | (v2_struct_0 @ sk_B)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['533', '593'])).
% 0.89/1.07  thf('595', plain, ((v10_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('596', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('597', plain, ((v7_waybel_0 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('598', plain, ((v4_orders_2 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('599', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_A)
% 0.89/1.07         | (v2_struct_0 @ sk_A)
% 0.89/1.07         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | (v2_struct_0 @ sk_B)
% 0.89/1.07         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | (v2_struct_0 @ sk_B)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('demod', [status(thm)], ['594', '595', '596', '597', '598'])).
% 0.89/1.07  thf('600', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_B)
% 0.89/1.07         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | (v2_struct_0 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('simplify', [status(thm)], ['599'])).
% 0.89/1.07  thf('601', plain, (~ (v2_struct_0 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('602', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_A)
% 0.89/1.07         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('clc', [status(thm)], ['600', '601'])).
% 0.89/1.07  thf('603', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('simplify', [status(thm)], ['80'])).
% 0.89/1.07  thf('604', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.07      inference('simplify', [status(thm)], ['76'])).
% 0.89/1.07  thf('605', plain,
% 0.89/1.07      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.89/1.07         ((v2_struct_0 @ X23)
% 0.89/1.07          | ~ (v4_orders_2 @ X23)
% 0.89/1.07          | ~ (v7_waybel_0 @ X23)
% 0.89/1.07          | ~ (l1_waybel_0 @ X23 @ X24)
% 0.89/1.07          | ~ (r3_waybel_9 @ X24 @ X23 @ X25)
% 0.89/1.07          | (r2_hidden @ X25 @ (k10_yellow_6 @ X24 @ X23))
% 0.89/1.07          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.89/1.07          | ((sk_C_2 @ X23 @ X24) != (sk_D_1 @ X23 @ X24))
% 0.89/1.07          | ~ (l1_pre_topc @ X24)
% 0.89/1.07          | ~ (v1_compts_1 @ X24)
% 0.89/1.07          | ~ (v8_pre_topc @ X24)
% 0.89/1.07          | ~ (v2_pre_topc @ X24)
% 0.89/1.07          | (v2_struct_0 @ X24))),
% 0.89/1.07      inference('cnf', [status(esa)], [t33_waybel_9])).
% 0.89/1.07  thf('606', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ sk_A)
% 0.89/1.07          | (v2_struct_0 @ sk_A)
% 0.89/1.07          | ~ (v2_pre_topc @ sk_A)
% 0.89/1.07          | ~ (v8_pre_topc @ sk_A)
% 0.89/1.07          | ~ (v1_compts_1 @ sk_A)
% 0.89/1.07          | ~ (l1_pre_topc @ sk_A)
% 0.89/1.07          | ((sk_C_2 @ X0 @ sk_A) != (sk_D_1 @ X0 @ sk_A))
% 0.89/1.07          | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07             (k10_yellow_6 @ sk_A @ X0))
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07          | ~ (v7_waybel_0 @ X0)
% 0.89/1.07          | ~ (v4_orders_2 @ X0)
% 0.89/1.07          | (v2_struct_0 @ X0))),
% 0.89/1.07      inference('sup-', [status(thm)], ['604', '605'])).
% 0.89/1.07  thf('607', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('608', plain, ((v8_pre_topc @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('609', plain, ((v1_compts_1 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('610', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.07      inference('sup-', [status(thm)], ['9', '10'])).
% 0.89/1.07  thf('611', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ sk_A)
% 0.89/1.07          | (v2_struct_0 @ sk_A)
% 0.89/1.07          | ((sk_C_2 @ X0 @ sk_A) != (sk_D_1 @ X0 @ sk_A))
% 0.89/1.07          | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07             (k10_yellow_6 @ sk_A @ X0))
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07          | ~ (v7_waybel_0 @ X0)
% 0.89/1.07          | ~ (v4_orders_2 @ X0)
% 0.89/1.07          | (v2_struct_0 @ X0))),
% 0.89/1.07      inference('demod', [status(thm)], ['606', '607', '608', '609', '610'])).
% 0.89/1.07  thf('612', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v2_struct_0 @ X0)
% 0.89/1.07          | ~ (v4_orders_2 @ X0)
% 0.89/1.07          | ~ (v7_waybel_0 @ X0)
% 0.89/1.07          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.89/1.07          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07          | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07             (k10_yellow_6 @ sk_A @ X0))
% 0.89/1.07          | ((sk_C_2 @ X0 @ sk_A) != (sk_D_1 @ X0 @ sk_A))
% 0.89/1.07          | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['611'])).
% 0.89/1.07  thf('613', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | ((sk_C_2 @ sk_B @ sk_A) != (sk_D_1 @ sk_B @ sk_A))
% 0.89/1.07        | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.89/1.07        | ~ (v7_waybel_0 @ sk_B)
% 0.89/1.07        | ~ (v4_orders_2 @ sk_B)
% 0.89/1.07        | (v2_struct_0 @ sk_B))),
% 0.89/1.07      inference('sup-', [status(thm)], ['603', '612'])).
% 0.89/1.07  thf('614', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('615', plain, ((v7_waybel_0 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('616', plain, ((v4_orders_2 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('617', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A)
% 0.89/1.07        | (v2_struct_0 @ sk_A)
% 0.89/1.07        | ((sk_C_2 @ sk_B @ sk_A) != (sk_D_1 @ sk_B @ sk_A))
% 0.89/1.07        | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07        | (v2_struct_0 @ sk_B))),
% 0.89/1.07      inference('demod', [status(thm)], ['613', '614', '615', '616'])).
% 0.89/1.07  thf('618', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_B)
% 0.89/1.07        | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07        | ((sk_C_2 @ sk_B @ sk_A) != (sk_D_1 @ sk_B @ sk_A))
% 0.89/1.07        | (v2_struct_0 @ sk_A))),
% 0.89/1.07      inference('simplify', [status(thm)], ['617'])).
% 0.89/1.07  thf('619', plain,
% 0.89/1.07      (((((sk_C_2 @ sk_B @ sk_A) != (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | (v2_struct_0 @ sk_A)
% 0.89/1.07         | (v2_struct_0 @ sk_A)
% 0.89/1.07         | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07            (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07         | (v2_struct_0 @ sk_B)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['602', '618'])).
% 0.89/1.07  thf('620', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_B)
% 0.89/1.07         | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07            (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07         | (v2_struct_0 @ sk_A)
% 0.89/1.07         | ((sk_C_2 @ sk_B @ sk_A) != (k1_waybel_2 @ sk_A @ sk_B))))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('simplify', [status(thm)], ['619'])).
% 0.89/1.07  thf('621', plain,
% 0.89/1.07      (((((k1_waybel_2 @ sk_A @ sk_B) != (k1_waybel_2 @ sk_A @ sk_B))
% 0.89/1.07         | (v2_struct_0 @ sk_A)
% 0.89/1.07         | (v2_struct_0 @ sk_A)
% 0.89/1.07         | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07            (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07         | (v2_struct_0 @ sk_B)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['513', '620'])).
% 0.89/1.07  thf('622', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_B)
% 0.89/1.07         | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07            (k10_yellow_6 @ sk_A @ sk_B))
% 0.89/1.07         | (v2_struct_0 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('simplify', [status(thm)], ['621'])).
% 0.89/1.07  thf('623', plain, (~ (v2_struct_0 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('624', plain,
% 0.89/1.07      ((((v2_struct_0 @ sk_A)
% 0.89/1.07         | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07            (k10_yellow_6 @ sk_A @ sk_B))))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('clc', [status(thm)], ['622', '623'])).
% 0.89/1.07  thf('625', plain,
% 0.89/1.07      ((~ (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07           (k10_yellow_6 @ sk_A @ sk_B)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('split', [status(esa)], ['419'])).
% 0.89/1.07  thf('626', plain,
% 0.89/1.07      (((v2_struct_0 @ sk_A))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('clc', [status(thm)], ['624', '625'])).
% 0.89/1.07  thf(cc1_lattice3, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( l1_orders_2 @ A ) =>
% 0.89/1.07       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.89/1.07  thf('627', plain,
% 0.89/1.07      (![X3 : $i]:
% 0.89/1.07         (~ (v1_lattice3 @ X3) | ~ (v2_struct_0 @ X3) | ~ (l1_orders_2 @ X3))),
% 0.89/1.07      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.89/1.07  thf('628', plain,
% 0.89/1.07      (((~ (l1_orders_2 @ sk_A) | ~ (v1_lattice3 @ sk_A)))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['626', '627'])).
% 0.89/1.07  thf('629', plain, ((v1_lattice3 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('630', plain,
% 0.89/1.07      ((~ (l1_orders_2 @ sk_A))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('demod', [status(thm)], ['628', '629'])).
% 0.89/1.07  thf('631', plain,
% 0.89/1.07      ((~ (l1_waybel_9 @ sk_A))
% 0.89/1.07         <= (~
% 0.89/1.07             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 0.89/1.07               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['421', '630'])).
% 0.89/1.07  thf('632', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('633', plain,
% 0.89/1.07      (((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('demod', [status(thm)], ['631', '632'])).
% 0.89/1.07  thf('634', plain,
% 0.89/1.07      (~ ((r1_waybel_9 @ sk_A @ sk_B)) | 
% 0.89/1.07       ~
% 0.89/1.07       ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('split', [status(esa)], ['419'])).
% 0.89/1.07  thf('635', plain, (~ ((r1_waybel_9 @ sk_A @ sk_B))),
% 0.89/1.07      inference('sat_resolution*', [status(thm)], ['633', '634'])).
% 0.89/1.07  thf('636', plain, (~ (r1_waybel_9 @ sk_A @ sk_B)),
% 0.89/1.07      inference('simpl_trail', [status(thm)], ['420', '635'])).
% 0.89/1.07  thf('637', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 0.89/1.07      inference('clc', [status(thm)], ['418', '636'])).
% 0.89/1.07  thf('638', plain, (~ (v2_struct_0 @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('639', plain, ((v2_struct_0 @ sk_A)),
% 0.89/1.07      inference('clc', [status(thm)], ['637', '638'])).
% 0.89/1.07  thf('640', plain,
% 0.89/1.07      (![X3 : $i]:
% 0.89/1.07         (~ (v1_lattice3 @ X3) | ~ (v2_struct_0 @ X3) | ~ (l1_orders_2 @ X3))),
% 0.89/1.07      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.89/1.07  thf('641', plain, ((~ (l1_orders_2 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 0.89/1.07      inference('sup-', [status(thm)], ['639', '640'])).
% 0.89/1.07  thf('642', plain, ((v1_lattice3 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('643', plain, (~ (l1_orders_2 @ sk_A)),
% 0.89/1.07      inference('demod', [status(thm)], ['641', '642'])).
% 0.89/1.07  thf('644', plain, (~ (l1_waybel_9 @ sk_A)),
% 0.89/1.07      inference('sup-', [status(thm)], ['0', '643'])).
% 0.89/1.07  thf('645', plain, ((l1_waybel_9 @ sk_A)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('646', plain, ($false), inference('demod', [status(thm)], ['644', '645'])).
% 0.89/1.07  
% 0.89/1.07  % SZS output end Refutation
% 0.89/1.07  
% 0.89/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
