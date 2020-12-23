%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3lqvdBIjSF

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:36 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  666 (33932 expanded)
%              Number of leaves         :   48 (10215 expanded)
%              Depth                    :  124
%              Number of atoms          : 11083 (1051101 expanded)
%              Number of equality atoms :   92 (2675 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k1_waybel_9_type,type,(
    k1_waybel_9: $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v11_waybel_0_type,type,(
    v11_waybel_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_waybel_9_type,type,(
    r2_waybel_9: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(dt_l1_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_waybel_9 @ A )
     => ( ( l1_pre_topc @ A )
        & ( l1_orders_2 @ A ) ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( l1_orders_2 @ X8 )
      | ~ ( l1_waybel_9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('1',plain,(
    ! [X8: $i] :
      ( ( l1_orders_2 @ X8 )
      | ~ ( l1_waybel_9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('2',plain,(
    ! [X8: $i] :
      ( ( l1_orders_2 @ X8 )
      | ~ ( l1_waybel_9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf(t39_waybel_9,conjecture,(
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
           => ( ( v11_waybel_0 @ B @ A )
             => ( ( r2_waybel_9 @ A @ B )
                & ( r2_hidden @ ( k1_waybel_9 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) )).

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
             => ( ( v11_waybel_0 @ B @ A )
               => ( ( r2_waybel_9 @ A @ B )
                  & ( r2_hidden @ ( k1_waybel_9 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_waybel_9])).

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
    ! [X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v7_waybel_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( r3_waybel_9 @ X19 @ X18 @ ( sk_C_1 @ X18 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v1_compts_1 @ X19 )
      | ~ ( v8_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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
    ! [X8: $i] :
      ( ( l1_pre_topc @ X8 )
      | ~ ( l1_waybel_9 @ X8 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v7_waybel_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( m1_subset_1 @ ( sk_C_1 @ X18 @ X19 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v1_compts_1 @ X19 )
      | ~ ( v8_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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

thf(t36_waybel_9,axiom,(
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
                  & ( v11_waybel_0 @ C @ A )
                  & ( r3_waybel_9 @ A @ C @ B ) )
               => ( B
                  = ( k1_waybel_9 @ A @ C ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X24 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v11_waybel_0 @ X25 @ X24 )
      | ~ ( r3_waybel_9 @ X24 @ X25 @ X23 )
      | ( X23
        = ( k1_waybel_9 @ X24 @ X25 ) )
      | ~ ( l1_waybel_0 @ X25 @ X24 )
      | ~ ( v7_waybel_0 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_waybel_9 @ X24 )
      | ~ ( v1_compts_1 @ X24 )
      | ~ ( v2_lattice3 @ X24 )
      | ~ ( v1_lattice3 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t36_waybel_9])).

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
        = ( k1_waybel_9 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
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
        = ( k1_waybel_9 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','35','36','37','38','39','40','41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v11_waybel_0 @ sk_B @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','42'])).

thf('44',plain,(
    v11_waybel_0 @ sk_B @ sk_A ),
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
      = ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X26: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X26 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_D_2 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X24 @ ( sk_D_2 @ X24 ) ) @ X24 @ X24 )
      | ~ ( v11_waybel_0 @ X25 @ X24 )
      | ~ ( r3_waybel_9 @ X24 @ X25 @ X23 )
      | ( X23
        = ( k1_waybel_9 @ X24 @ X25 ) )
      | ~ ( l1_waybel_0 @ X25 @ X24 )
      | ~ ( v7_waybel_0 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_waybel_9 @ X24 )
      | ~ ( v1_compts_1 @ X24 )
      | ~ ( v2_lattice3 @ X24 )
      | ~ ( v1_lattice3 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t36_waybel_9])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
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
        = ( k1_waybel_9 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
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
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( X1
        = ( k1_waybel_9 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57','58','59','60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v11_waybel_0 @ sk_B @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','65'])).

thf('67',plain,(
    v11_waybel_0 @ sk_B @ sk_A ),
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
      = ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('76',plain,
    ( ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('79',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('80',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('83',plain,(
    ! [X8: $i] :
      ( ( l1_orders_2 @ X8 )
      | ~ ( l1_waybel_9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('84',plain,(
    ! [X8: $i] :
      ( ( l1_orders_2 @ X8 )
      | ~ ( l1_waybel_9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('87',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('88',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(l51_waybel_9,axiom,(
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
                      & ( v11_waybel_0 @ B @ A )
                      & ( r3_waybel_9 @ A @ B @ C ) )
                   => ( r1_lattice3 @ A @ ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) ) @ D ) ) ) ) ) ) )).

thf('89',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v4_orders_2 @ X9 )
      | ~ ( v7_waybel_0 @ X9 )
      | ~ ( l1_waybel_0 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( r1_lattice3 @ X10 @ ( k2_relset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X10 ) @ ( u1_waybel_0 @ X10 @ X9 ) ) @ X11 )
      | ( X12 != X11 )
      | ~ ( r3_waybel_9 @ X10 @ X9 @ X12 )
      | ~ ( v11_waybel_0 @ X9 @ X10 )
      | ( m1_subset_1 @ ( sk_E @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_waybel_9 @ X10 )
      | ~ ( v1_compts_1 @ X10 )
      | ~ ( v2_lattice3 @ X10 )
      | ~ ( v1_lattice3 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ~ ( v8_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_waybel_9])).

thf('90',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v2_pre_topc @ X10 )
      | ~ ( v8_pre_topc @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v1_lattice3 @ X10 )
      | ~ ( v2_lattice3 @ X10 )
      | ~ ( v1_compts_1 @ X10 )
      | ~ ( l1_waybel_9 @ X10 )
      | ( m1_subset_1 @ ( sk_E @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v11_waybel_0 @ X9 @ X10 )
      | ~ ( r3_waybel_9 @ X10 @ X9 @ X11 )
      | ( r1_lattice3 @ X10 @ ( k2_relset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X10 ) @ ( u1_waybel_0 @ X10 @ X9 ) ) @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_waybel_0 @ X9 @ X10 )
      | ~ ( v7_waybel_0 @ X9 )
      | ~ ( v4_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
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
      | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95','96','97','98','99','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v11_waybel_0 @ sk_B @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','101'])).

thf('103',plain,(
    v11_waybel_0 @ sk_B @ sk_A ),
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
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['102','103','104','105','106'])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['86','108'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('113',plain,(
    ! [X8: $i] :
      ( ( l1_orders_2 @ X8 )
      | ~ ( l1_waybel_9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('114',plain,(
    ! [X8: $i] :
      ( ( l1_orders_2 @ X8 )
      | ~ ( l1_waybel_9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['107'])).

thf('121',plain,(
    ! [X8: $i] :
      ( ( l1_orders_2 @ X8 )
      | ~ ( l1_waybel_9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('122',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(t16_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( r2_yellow_0 @ A @ B )
        <=> ? [C: $i] :
              ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r1_lattice3 @ A @ B @ D )
                   => ( r1_orders_2 @ A @ D @ C ) ) )
              & ( r1_lattice3 @ A @ B @ C )
              & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('123',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X1 @ X2 @ X3 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( r1_lattice3 @ X3 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X3 ) )
      | ( r2_yellow_0 @ X3 @ X2 )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v5_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t16_yellow_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','126'])).

thf('128',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','129'])).

thf('131',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['119','131'])).

thf('133',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['107'])).

thf('136',plain,(
    ! [X8: $i] :
      ( ( l1_orders_2 @ X8 )
      | ~ ( l1_waybel_9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('137',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('138',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r1_lattice3 @ X3 @ X2 @ ( sk_D @ X1 @ X2 @ X3 ) )
      | ~ ( r1_lattice3 @ X3 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X3 ) )
      | ( r2_yellow_0 @ X3 @ X2 )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v5_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t16_yellow_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['136','141'])).

thf('143',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['135','144'])).

thf('146',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['134','146'])).

thf('148',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf(l52_waybel_9,axiom,(
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
                       => ( ( r1_lattice3 @ A @ ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) ) @ E )
                         => ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) )).

thf('149',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v7_waybel_0 @ X13 )
      | ~ ( l1_waybel_0 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r1_lattice3 @ X14 @ ( k2_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) @ ( u1_waybel_0 @ X14 @ X13 ) ) @ X16 )
      | ( r1_orders_2 @ X14 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ( X17 != X15 )
      | ~ ( r3_waybel_9 @ X14 @ X13 @ X17 )
      | ( m1_subset_1 @ ( sk_E_1 @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_waybel_9 @ X14 )
      | ~ ( v1_compts_1 @ X14 )
      | ~ ( v2_lattice3 @ X14 )
      | ~ ( v1_lattice3 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ~ ( v8_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[l52_waybel_9])).

thf('150',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v2_pre_topc @ X14 )
      | ~ ( v8_pre_topc @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v1_lattice3 @ X14 )
      | ~ ( v2_lattice3 @ X14 )
      | ~ ( v1_compts_1 @ X14 )
      | ~ ( l1_waybel_9 @ X14 )
      | ( m1_subset_1 @ ( sk_E_1 @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( r3_waybel_9 @ X14 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ( r1_orders_2 @ X14 @ X16 @ X15 )
      | ~ ( r1_lattice3 @ X14 @ ( k2_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) @ ( u1_waybel_0 @ X14 @ X13 ) ) @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_waybel_0 @ X13 @ X14 )
      | ~ ( v7_waybel_0 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
    inference('sup-',[status(thm)],['148','150'])).

thf('152',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['151','152','153','154','155','156','157','158','159','160','161','162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['133','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','167'])).

thf('169',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','169'])).

thf('171',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_orders_2 @ X3 @ ( sk_D @ X1 @ X2 @ X3 ) @ X1 )
      | ~ ( r1_lattice3 @ X3 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X3 ) )
      | ( r2_yellow_0 @ X3 @ X2 )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v5_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t16_yellow_0])).

thf('173',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','176'])).

thf('178',plain,
    ( ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['115','178'])).

thf('180',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','180'])).

thf('182',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf(d4_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( ( r2_waybel_9 @ A @ B )
          <=> ( r2_yellow_0 @ A @ ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) ) ) ) ) ) )).

thf('184',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_waybel_0 @ X6 @ X7 )
      | ~ ( r2_yellow_0 @ X7 @ ( k2_relset_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X7 ) @ ( u1_waybel_0 @ X7 @ X6 ) ) )
      | ( r2_waybel_9 @ X7 @ X6 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_waybel_9])).

thf('185',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','187'])).

thf('189',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X26: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X26 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('194',plain,
    ( ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('195',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v7_waybel_0 @ X13 )
      | ~ ( l1_waybel_0 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r1_lattice3 @ X14 @ ( k2_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) @ ( u1_waybel_0 @ X14 @ X13 ) ) @ X16 )
      | ( r1_orders_2 @ X14 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ( X17 != X15 )
      | ~ ( r3_waybel_9 @ X14 @ X13 @ X17 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X14 @ ( sk_E_1 @ X14 ) ) @ X14 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_waybel_9 @ X14 )
      | ~ ( v1_compts_1 @ X14 )
      | ~ ( v2_lattice3 @ X14 )
      | ~ ( v1_lattice3 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ~ ( v8_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[l52_waybel_9])).

thf('196',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v2_pre_topc @ X14 )
      | ~ ( v8_pre_topc @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v1_lattice3 @ X14 )
      | ~ ( v2_lattice3 @ X14 )
      | ~ ( v1_compts_1 @ X14 )
      | ~ ( l1_waybel_9 @ X14 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X14 @ ( sk_E_1 @ X14 ) ) @ X14 @ X14 )
      | ~ ( r3_waybel_9 @ X14 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ( r1_orders_2 @ X14 @ X16 @ X15 )
      | ~ ( r1_lattice3 @ X14 @ ( k2_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) @ ( u1_waybel_0 @ X14 @ X13 ) ) @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_waybel_0 @ X13 @ X14 )
      | ~ ( v7_waybel_0 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
    inference('sup-',[status(thm)],['194','196'])).

thf('198',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['197','198','199','200','201','202','203','204','205','206','207','208','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['193','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['192','213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['112','215'])).

thf('217',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['216'])).

thf('218',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['111','217'])).

thf('219',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_orders_2 @ X3 @ ( sk_D @ X1 @ X2 @ X3 ) @ X1 )
      | ~ ( r1_lattice3 @ X3 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X3 ) )
      | ( r2_yellow_0 @ X3 @ X2 )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v5_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t16_yellow_0])).

thf('221',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('224',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','224'])).

thf('226',plain,
    ( ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','226'])).

thf('228',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','228'])).

thf('230',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_waybel_0 @ X6 @ X7 )
      | ~ ( r2_yellow_0 @ X7 @ ( k2_relset_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X7 ) @ ( u1_waybel_0 @ X7 @ X6 ) ) )
      | ( r2_waybel_9 @ X7 @ X6 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_waybel_9])).

thf('233',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['235'])).

thf('237',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','236'])).

thf('238',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,(
    ! [X26: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X26 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v4_orders_2 @ X9 )
      | ~ ( v7_waybel_0 @ X9 )
      | ~ ( l1_waybel_0 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( r1_lattice3 @ X10 @ ( k2_relset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X10 ) @ ( u1_waybel_0 @ X10 @ X9 ) ) @ X11 )
      | ( X12 != X11 )
      | ~ ( r3_waybel_9 @ X10 @ X9 @ X12 )
      | ~ ( v11_waybel_0 @ X9 @ X10 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X10 @ ( sk_E @ X10 ) ) @ X10 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_waybel_9 @ X10 )
      | ~ ( v1_compts_1 @ X10 )
      | ~ ( v2_lattice3 @ X10 )
      | ~ ( v1_lattice3 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ~ ( v8_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_waybel_9])).

thf('243',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v2_pre_topc @ X10 )
      | ~ ( v8_pre_topc @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v1_lattice3 @ X10 )
      | ~ ( v2_lattice3 @ X10 )
      | ~ ( v1_compts_1 @ X10 )
      | ~ ( l1_waybel_9 @ X10 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X10 @ ( sk_E @ X10 ) ) @ X10 @ X10 )
      | ~ ( v11_waybel_0 @ X9 @ X10 )
      | ~ ( r3_waybel_9 @ X10 @ X9 @ X11 )
      | ( r1_lattice3 @ X10 @ ( k2_relset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X10 ) @ ( u1_waybel_0 @ X10 @ X9 ) ) @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_waybel_0 @ X9 @ X10 )
      | ~ ( v7_waybel_0 @ X9 )
      | ~ ( v4_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['242'])).

thf('244',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ X1 )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
      | ~ ( l1_waybel_9 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( v2_lattice3 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['241','243'])).

thf('245',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ X1 )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
      | ~ ( v11_waybel_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['244','245','246','247','248','249','250','251','252','253'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','254'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( v11_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['255'])).

thf('257',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v11_waybel_0 @ sk_B @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['81','256'])).

thf('258',plain,(
    v11_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['257','258','259','260','261'])).

thf('263',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['262'])).

thf('264',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('265',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('266',plain,(
    ! [X8: $i] :
      ( ( l1_orders_2 @ X8 )
      | ~ ( l1_waybel_9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('267',plain,(
    ! [X8: $i] :
      ( ( l1_orders_2 @ X8 )
      | ~ ( l1_waybel_9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('268',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('269',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['262'])).

thf('270',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('271',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('272',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['262'])).

thf('273',plain,(
    ! [X8: $i] :
      ( ( l1_orders_2 @ X8 )
      | ~ ( l1_waybel_9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('274',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('275',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X1 @ X2 @ X3 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( r1_lattice3 @ X3 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X3 ) )
      | ( r2_yellow_0 @ X3 @ X2 )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v5_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t16_yellow_0])).

thf('276',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['274','275'])).

thf('277',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['276','277'])).

thf('279',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( r2_yellow_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['273','278'])).

thf('280',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( r2_yellow_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['279','280'])).

thf('282',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['272','281'])).

thf('283',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['282'])).

thf('284',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['262'])).

thf('285',plain,(
    ! [X8: $i] :
      ( ( l1_orders_2 @ X8 )
      | ~ ( l1_waybel_9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('286',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('287',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r1_lattice3 @ X3 @ X2 @ ( sk_D @ X1 @ X2 @ X3 ) )
      | ~ ( r1_lattice3 @ X3 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X3 ) )
      | ( r2_yellow_0 @ X3 @ X2 )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v5_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t16_yellow_0])).

thf('288',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['286','287'])).

thf('289',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_yellow_0 @ sk_A @ X0 )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['288','289'])).

thf('291',plain,(
    ! [X0: $i] :
      ( ~ ( l1_waybel_9 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( r2_yellow_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['285','290'])).

thf('292',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ X0 @ sk_A ) )
      | ~ ( r1_lattice3 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( r2_yellow_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['291','292'])).

thf('294',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['284','293'])).

thf('295',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['294'])).

thf('296',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v2_pre_topc @ X14 )
      | ~ ( v8_pre_topc @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v1_lattice3 @ X14 )
      | ~ ( v2_lattice3 @ X14 )
      | ~ ( v1_compts_1 @ X14 )
      | ~ ( l1_waybel_9 @ X14 )
      | ( m1_subset_1 @ ( sk_E_1 @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( r3_waybel_9 @ X14 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ( r1_orders_2 @ X14 @ X16 @ X15 )
      | ~ ( r1_lattice3 @ X14 @ ( k2_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) @ ( u1_waybel_0 @ X14 @ X13 ) ) @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_waybel_0 @ X13 @ X14 )
      | ~ ( v7_waybel_0 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('297',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
    inference('sup-',[status(thm)],['295','296'])).

thf('298',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['297','298','299','300','301','302','303','304','305','306','307','308','309'])).

thf('311',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['310'])).

thf('312',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['283','311'])).

thf('313',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['312'])).

thf('314',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['271','313'])).

thf('315',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['314'])).

thf('316',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['270','315'])).

thf('317',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['316'])).

thf('318',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_orders_2 @ X3 @ ( sk_D @ X1 @ X2 @ X3 ) @ X1 )
      | ~ ( r1_lattice3 @ X3 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X3 ) )
      | ( r2_yellow_0 @ X3 @ X2 )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v5_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t16_yellow_0])).

thf('319',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['317','318'])).

thf('320',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('321',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['319','320'])).

thf('322',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['321'])).

thf('323',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['269','322'])).

thf('324',plain,
    ( ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['323'])).

thf('325',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['268','324'])).

thf('326',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['325'])).

thf('327',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['267','326'])).

thf('328',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['327','328'])).

thf('330',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_waybel_0 @ X6 @ X7 )
      | ~ ( r2_yellow_0 @ X7 @ ( k2_relset_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X7 ) @ ( u1_waybel_0 @ X7 @ X6 ) ) )
      | ( r2_waybel_9 @ X7 @ X6 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_waybel_9])).

thf('331',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['329','330'])).

thf('332',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['331','332'])).

thf('334',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['333'])).

thf('335',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['266','334'])).

thf('336',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('337',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['335','336'])).

thf('338',plain,(
    ! [X26: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X26 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('339',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['337','338'])).

thf('340',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['282'])).

thf('341',plain,
    ( ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['294'])).

thf('342',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v2_pre_topc @ X14 )
      | ~ ( v8_pre_topc @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v1_lattice3 @ X14 )
      | ~ ( v2_lattice3 @ X14 )
      | ~ ( v1_compts_1 @ X14 )
      | ~ ( l1_waybel_9 @ X14 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X14 @ ( sk_E_1 @ X14 ) ) @ X14 @ X14 )
      | ~ ( r3_waybel_9 @ X14 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ( r1_orders_2 @ X14 @ X16 @ X15 )
      | ~ ( r1_lattice3 @ X14 @ ( k2_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) @ ( u1_waybel_0 @ X14 @ X13 ) ) @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_waybel_0 @ X13 @ X14 )
      | ~ ( v7_waybel_0 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('343',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
    inference('sup-',[status(thm)],['341','342'])).

thf('344',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('345',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('346',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('348',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('350',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('351',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('352',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('353',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('354',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('355',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('356',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['343','344','345','346','347','348','349','350','351','352','353','354','355'])).

thf('357',plain,(
    ! [X0: $i] :
      ( ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['356'])).

thf('358',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['340','357'])).

thf('359',plain,(
    ! [X0: $i] :
      ( ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['358'])).

thf('360',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['339','359'])).

thf('361',plain,(
    ! [X0: $i] :
      ( ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['360'])).

thf('362',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['265','361'])).

thf('363',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['362'])).

thf('364',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['264','363'])).

thf('365',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ sk_A ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['364'])).

thf('366',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_orders_2 @ X3 @ ( sk_D @ X1 @ X2 @ X3 ) @ X1 )
      | ~ ( r1_lattice3 @ X3 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X3 ) )
      | ( r2_yellow_0 @ X3 @ X2 )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v5_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t16_yellow_0])).

thf('367',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['365','366'])).

thf('368',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('369',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['367','368'])).

thf('370',plain,
    ( ~ ( r1_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_9 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['369'])).

thf('371',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['263','370'])).

thf('372',plain,
    ( ~ ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['371'])).

thf('373',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','372'])).

thf('374',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['373'])).

thf('375',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','374'])).

thf('376',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('377',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( r2_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['375','376'])).

thf('378',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_waybel_0 @ X6 @ X7 )
      | ~ ( r2_yellow_0 @ X7 @ ( k2_relset_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X7 ) @ ( u1_waybel_0 @ X7 @ X6 ) ) )
      | ( r2_waybel_9 @ X7 @ X6 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_waybel_9])).

thf('379',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['377','378'])).

thf('380',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('381',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['379','380'])).

thf('382',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['381'])).

thf('383',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
    | ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','382'])).

thf('384',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('385',plain,
    ( ( r2_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['383','384'])).

thf('386',plain,
    ( ~ ( r2_waybel_9 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('387',plain,
    ( ~ ( r2_waybel_9 @ sk_A @ sk_B )
   <= ~ ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['386'])).

thf('388',plain,(
    ! [X8: $i] :
      ( ( l1_orders_2 @ X8 )
      | ~ ( l1_waybel_9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('389',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('390',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('391',plain,
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

thf('392',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v7_waybel_0 @ X20 )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( r3_waybel_9 @ X21 @ X20 @ X22 )
      | ( r2_hidden @ X22 @ ( k10_yellow_6 @ X21 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( r3_waybel_9 @ X21 @ X20 @ ( sk_C_2 @ X20 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_compts_1 @ X21 )
      | ~ ( v8_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('393',plain,(
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
    inference('sup-',[status(thm)],['391','392'])).

thf('394',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('395',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('396',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('397',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('398',plain,(
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
    inference(demod,[status(thm)],['393','394','395','396','397'])).

thf('399',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_2 @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['398'])).

thf('400',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['390','399'])).

thf('401',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('402',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('403',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('404',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['400','401','402','403'])).

thf('405',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['404'])).

thf('406',plain,
    ( ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['389','405'])).

thf('407',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['406'])).

thf('408',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['386'])).

thf('409',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['407','408'])).

thf('410',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('411',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['409','410'])).

thf('412',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('413',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('414',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('415',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v7_waybel_0 @ X20 )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( r3_waybel_9 @ X21 @ X20 @ X22 )
      | ( r2_hidden @ X22 @ ( k10_yellow_6 @ X21 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( m1_subset_1 @ ( sk_C_2 @ X20 @ X21 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_compts_1 @ X21 )
      | ~ ( v8_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('416',plain,(
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
    inference('sup-',[status(thm)],['414','415'])).

thf('417',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('418',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('419',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('420',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('421',plain,(
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
    inference(demod,[status(thm)],['416','417','418','419','420'])).

thf('422',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_C_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['421'])).

thf('423',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['413','422'])).

thf('424',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('425',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('426',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('427',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['423','424','425','426'])).

thf('428',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['427'])).

thf('429',plain,
    ( ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['412','428'])).

thf('430',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['429'])).

thf('431',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['386'])).

thf('432',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['430','431'])).

thf('433',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('434',plain,
    ( ( ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['432','433'])).

thf('435',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['409','410'])).

thf('436',plain,
    ( ( ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['432','433'])).

thf('437',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X24 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v11_waybel_0 @ X25 @ X24 )
      | ~ ( r3_waybel_9 @ X24 @ X25 @ X23 )
      | ( X23
        = ( k1_waybel_9 @ X24 @ X25 ) )
      | ~ ( l1_waybel_0 @ X25 @ X24 )
      | ~ ( v7_waybel_0 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_waybel_9 @ X24 )
      | ~ ( v1_compts_1 @ X24 )
      | ~ ( v2_lattice3 @ X24 )
      | ~ ( v1_lattice3 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t36_waybel_9])).

thf('438',plain,
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
          = ( k1_waybel_9 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_2 @ sk_B @ sk_A ) )
        | ~ ( v11_waybel_0 @ X0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['436','437'])).

thf('439',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('440',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('441',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('442',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('443',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('444',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('445',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('446',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('447',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('448',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( ( sk_C_2 @ sk_B @ sk_A )
          = ( k1_waybel_9 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_2 @ sk_B @ sk_A ) )
        | ~ ( v11_waybel_0 @ X0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['438','439','440','441','442','443','444','445','446','447'])).

thf('449',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v11_waybel_0 @ sk_B @ sk_A )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['435','448'])).

thf('450',plain,(
    v11_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('451',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('452',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('453',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('454',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['449','450','451','452','453'])).

thf('455',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['454'])).

thf('456',plain,(
    ! [X26: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X26 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('457',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_D_2 @ sk_A ) ) @ sk_A @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['455','456'])).

thf('458',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X24 @ ( sk_D_2 @ X24 ) ) @ X24 @ X24 )
      | ~ ( v11_waybel_0 @ X25 @ X24 )
      | ~ ( r3_waybel_9 @ X24 @ X25 @ X23 )
      | ( X23
        = ( k1_waybel_9 @ X24 @ X25 ) )
      | ~ ( l1_waybel_0 @ X25 @ X24 )
      | ~ ( v7_waybel_0 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_waybel_9 @ X24 )
      | ~ ( v1_compts_1 @ X24 )
      | ~ ( v2_lattice3 @ X24 )
      | ~ ( v1_lattice3 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t36_waybel_9])).

thf('459',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( ( sk_C_2 @ sk_B @ sk_A )
          = ( k1_waybel_9 @ sk_A @ sk_B ) )
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
          = ( k1_waybel_9 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
        | ~ ( v11_waybel_0 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['457','458'])).

thf('460',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('461',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('462',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('463',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('464',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('465',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('466',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('467',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('468',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('469',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( ( sk_C_2 @ sk_B @ sk_A )
          = ( k1_waybel_9 @ sk_A @ sk_B ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( X1
          = ( k1_waybel_9 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
        | ~ ( v11_waybel_0 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['459','460','461','462','463','464','465','466','467','468'])).

thf('470',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v11_waybel_0 @ X0 @ sk_A )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_2 @ sk_B @ sk_A ) )
        | ( ( sk_C_2 @ sk_B @ sk_A )
          = ( k1_waybel_9 @ sk_A @ X0 ) )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_C_2 @ sk_B @ sk_A )
          = ( k1_waybel_9 @ sk_A @ sk_B ) )
        | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['434','469'])).

thf('471',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( ( sk_C_2 @ sk_B @ sk_A )
          = ( k1_waybel_9 @ sk_A @ sk_B ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( ( sk_C_2 @ sk_B @ sk_A )
          = ( k1_waybel_9 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_2 @ sk_B @ sk_A ) )
        | ~ ( v11_waybel_0 @ X0 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['470'])).

thf('472',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v11_waybel_0 @ sk_B @ sk_A )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['411','471'])).

thf('473',plain,(
    v11_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('474',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('475',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('476',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('477',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['472','473','474','475','476'])).

thf('478',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['477'])).

thf('479',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('480',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( sk_C_2 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['478','479'])).

thf('481',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('482',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('483',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('484',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v7_waybel_0 @ X20 )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( r3_waybel_9 @ X21 @ X20 @ X22 )
      | ( r2_hidden @ X22 @ ( k10_yellow_6 @ X21 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( r3_waybel_9 @ X21 @ X20 @ ( sk_D_1 @ X20 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_compts_1 @ X21 )
      | ~ ( v8_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('485',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['483','484'])).

thf('486',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('487',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('488',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('489',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('490',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['485','486','487','488','489'])).

thf('491',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['490'])).

thf('492',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['482','491'])).

thf('493',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('494',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('495',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('496',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['492','493','494','495'])).

thf('497',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['496'])).

thf('498',plain,
    ( ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['481','497'])).

thf('499',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['498'])).

thf('500',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['386'])).

thf('501',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['499','500'])).

thf('502',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('503',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['501','502'])).

thf('504',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
      = ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('505',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('506',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('507',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v7_waybel_0 @ X20 )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( r3_waybel_9 @ X21 @ X20 @ X22 )
      | ( r2_hidden @ X22 @ ( k10_yellow_6 @ X21 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X20 @ X21 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_compts_1 @ X21 )
      | ~ ( v8_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('508',plain,(
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
    inference('sup-',[status(thm)],['506','507'])).

thf('509',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('510',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('511',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('512',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('513',plain,(
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
    inference(demod,[status(thm)],['508','509','510','511','512'])).

thf('514',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['513'])).

thf('515',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['505','514'])).

thf('516',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('517',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('518',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('519',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['515','516','517','518'])).

thf('520',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['519'])).

thf('521',plain,
    ( ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['504','520'])).

thf('522',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['521'])).

thf('523',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['386'])).

thf('524',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['522','523'])).

thf('525',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('526',plain,
    ( ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['524','525'])).

thf('527',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['501','502'])).

thf('528',plain,
    ( ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['524','525'])).

thf('529',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X24 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v11_waybel_0 @ X25 @ X24 )
      | ~ ( r3_waybel_9 @ X24 @ X25 @ X23 )
      | ( X23
        = ( k1_waybel_9 @ X24 @ X25 ) )
      | ~ ( l1_waybel_0 @ X25 @ X24 )
      | ~ ( v7_waybel_0 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_waybel_9 @ X24 )
      | ~ ( v1_compts_1 @ X24 )
      | ~ ( v2_lattice3 @ X24 )
      | ~ ( v1_lattice3 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t36_waybel_9])).

thf('530',plain,
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
          = ( k1_waybel_9 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ sk_A ) )
        | ~ ( v11_waybel_0 @ X0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['528','529'])).

thf('531',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('532',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('533',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('534',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('535',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('536',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('537',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('538',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('539',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('540',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( ( sk_D_1 @ sk_B @ sk_A )
          = ( k1_waybel_9 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ sk_A ) )
        | ~ ( v11_waybel_0 @ X0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['530','531','532','533','534','535','536','537','538','539'])).

thf('541',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v11_waybel_0 @ sk_B @ sk_A )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['527','540'])).

thf('542',plain,(
    v11_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('543',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('544',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('545',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('546',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['541','542','543','544','545'])).

thf('547',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['546'])).

thf('548',plain,(
    ! [X26: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X26 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('549',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_D_2 @ sk_A ) ) @ sk_A @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['547','548'])).

thf('550',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X24 @ ( sk_D_2 @ X24 ) ) @ X24 @ X24 )
      | ~ ( v11_waybel_0 @ X25 @ X24 )
      | ~ ( r3_waybel_9 @ X24 @ X25 @ X23 )
      | ( X23
        = ( k1_waybel_9 @ X24 @ X25 ) )
      | ~ ( l1_waybel_0 @ X25 @ X24 )
      | ~ ( v7_waybel_0 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_waybel_9 @ X24 )
      | ~ ( v1_compts_1 @ X24 )
      | ~ ( v2_lattice3 @ X24 )
      | ~ ( v1_lattice3 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t36_waybel_9])).

thf('551',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( ( sk_D_1 @ sk_B @ sk_A )
          = ( k1_waybel_9 @ sk_A @ sk_B ) )
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
          = ( k1_waybel_9 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
        | ~ ( v11_waybel_0 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['549','550'])).

thf('552',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('553',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('554',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('555',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('556',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('557',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('558',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('559',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('560',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('561',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( ( sk_D_1 @ sk_B @ sk_A )
          = ( k1_waybel_9 @ sk_A @ sk_B ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( X1
          = ( k1_waybel_9 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
        | ~ ( v11_waybel_0 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['551','552','553','554','555','556','557','558','559','560'])).

thf('562',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v11_waybel_0 @ X0 @ sk_A )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ sk_A ) )
        | ( ( sk_D_1 @ sk_B @ sk_A )
          = ( k1_waybel_9 @ sk_A @ X0 ) )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( ( sk_D_1 @ sk_B @ sk_A )
          = ( k1_waybel_9 @ sk_A @ sk_B ) )
        | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['526','561'])).

thf('563',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( ( sk_D_1 @ sk_B @ sk_A )
          = ( k1_waybel_9 @ sk_A @ sk_B ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( ( sk_D_1 @ sk_B @ sk_A )
          = ( k1_waybel_9 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ sk_B @ sk_A ) )
        | ~ ( v11_waybel_0 @ X0 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['562'])).

thf('564',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v11_waybel_0 @ sk_B @ sk_A )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['503','563'])).

thf('565',plain,(
    v11_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('566',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('567',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('568',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('569',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['564','565','566','567','568'])).

thf('570',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['569'])).

thf('571',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('572',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_9 @ sk_A @ sk_B ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['570','571'])).

thf('573',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_9 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('574',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('575',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v7_waybel_0 @ X20 )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( r3_waybel_9 @ X21 @ X20 @ X22 )
      | ( r2_hidden @ X22 @ ( k10_yellow_6 @ X21 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( ( sk_C_2 @ X20 @ X21 )
       != ( sk_D_1 @ X20 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_compts_1 @ X21 )
      | ~ ( v8_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('576',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( ( sk_C_2 @ X0 @ sk_A )
       != ( sk_D_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['574','575'])).

thf('577',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('578',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('579',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('580',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('581',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C_2 @ X0 @ sk_A )
       != ( sk_D_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['576','577','578','579','580'])).

thf('582',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( ( sk_C_2 @ X0 @ sk_A )
       != ( sk_D_1 @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['581'])).

thf('583',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_C_2 @ sk_B @ sk_A )
     != ( sk_D_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['573','582'])).

thf('584',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('585',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('586',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('587',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_C_2 @ sk_B @ sk_A )
     != ( sk_D_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['583','584','585','586'])).

thf('588',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( ( sk_C_2 @ sk_B @ sk_A )
     != ( sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['587'])).

thf('589',plain,
    ( ( ( ( sk_C_2 @ sk_B @ sk_A )
       != ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['572','588'])).

thf('590',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C_2 @ sk_B @ sk_A )
       != ( k1_waybel_9 @ sk_A @ sk_B ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['589'])).

thf('591',plain,
    ( ( ( ( k1_waybel_9 @ sk_A @ sk_B )
       != ( k1_waybel_9 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['480','590'])).

thf('592',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['591'])).

thf('593',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('594',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['592','593'])).

thf('595',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['386'])).

thf('596',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['594','595'])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('597',plain,(
    ! [X0: $i] :
      ( ~ ( v1_lattice3 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('598',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['596','597'])).

thf('599',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('600',plain,
    ( ~ ( l1_orders_2 @ sk_A )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['598','599'])).

thf('601',plain,
    ( ~ ( l1_waybel_9 @ sk_A )
   <= ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['388','600'])).

thf('602',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('603',plain,(
    r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['601','602'])).

thf('604',plain,
    ( ~ ( r2_waybel_9 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ ( k1_waybel_9 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['386'])).

thf('605',plain,(
    ~ ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['603','604'])).

thf('606',plain,(
    ~ ( r2_waybel_9 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['387','605'])).

thf('607',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['385','606'])).

thf('608',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('609',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['607','608'])).

thf('610',plain,(
    ! [X0: $i] :
      ( ~ ( v1_lattice3 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('611',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['609','610'])).

thf('612',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('613',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['611','612'])).

thf('614',plain,(
    ~ ( l1_waybel_9 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','613'])).

thf('615',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('616',plain,(
    $false ),
    inference(demod,[status(thm)],['614','615'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3lqvdBIjSF
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:27:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.75/0.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.95  % Solved by: fo/fo7.sh
% 0.75/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.95  % done 645 iterations in 0.480s
% 0.75/0.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.95  % SZS output start Refutation
% 0.75/0.95  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.75/0.95  thf(k1_waybel_9_type, type, k1_waybel_9: $i > $i > $i).
% 0.75/0.95  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.75/0.95  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.75/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.95  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 0.75/0.95  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.75/0.95  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.75/0.95  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.75/0.95  thf(sk_D_2_type, type, sk_D_2: $i > $i).
% 0.75/0.95  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.75/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.95  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.75/0.95  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.75/0.95  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.75/0.95  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.75/0.95  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.75/0.95  thf(sk_E_type, type, sk_E: $i > $i).
% 0.75/0.95  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 0.75/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.95  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.75/0.95  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 0.75/0.95  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.75/0.95  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.75/0.95  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.75/0.95  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.75/0.95  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 0.75/0.95  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.75/0.95  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.75/0.95  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 0.75/0.95  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.75/0.95  thf(v11_waybel_0_type, type, v11_waybel_0: $i > $i > $o).
% 0.75/0.95  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.75/0.95  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.75/0.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.95  thf(r2_waybel_9_type, type, r2_waybel_9: $i > $i > $o).
% 0.75/0.95  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.75/0.95  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.75/0.95  thf(dt_l1_waybel_9, axiom,
% 0.75/0.95    (![A:$i]:
% 0.75/0.95     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 0.75/0.95  thf('0', plain, (![X8 : $i]: ((l1_orders_2 @ X8) | ~ (l1_waybel_9 @ X8))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.75/0.95  thf('1', plain, (![X8 : $i]: ((l1_orders_2 @ X8) | ~ (l1_waybel_9 @ X8))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.75/0.95  thf('2', plain, (![X8 : $i]: ((l1_orders_2 @ X8) | ~ (l1_waybel_9 @ X8))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.75/0.95  thf(t39_waybel_9, conjecture,
% 0.75/0.95    (![A:$i]:
% 0.75/0.95     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.75/0.95         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.75/0.95         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.75/0.95       ( ( ![B:$i]:
% 0.75/0.95           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.75/0.95             ( v5_pre_topc @ ( k4_waybel_1 @ A @ B ) @ A @ A ) ) ) =>
% 0.75/0.95         ( ![B:$i]:
% 0.75/0.95           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.75/0.95               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.75/0.95             ( ( v11_waybel_0 @ B @ A ) =>
% 0.75/0.95               ( ( r2_waybel_9 @ A @ B ) & 
% 0.75/0.95                 ( r2_hidden @
% 0.75/0.95                   ( k1_waybel_9 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ))).
% 0.75/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.95    (~( ![A:$i]:
% 0.75/0.95        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.75/0.95            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.75/0.95            ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.75/0.95          ( ( ![B:$i]:
% 0.75/0.95              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.75/0.95                ( v5_pre_topc @ ( k4_waybel_1 @ A @ B ) @ A @ A ) ) ) =>
% 0.75/0.95            ( ![B:$i]:
% 0.75/0.95              ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.75/0.95                  ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.75/0.95                ( ( v11_waybel_0 @ B @ A ) =>
% 0.75/0.95                  ( ( r2_waybel_9 @ A @ B ) & 
% 0.75/0.95                    ( r2_hidden @
% 0.75/0.95                      ( k1_waybel_9 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ) )),
% 0.75/0.95    inference('cnf.neg', [status(esa)], [t39_waybel_9])).
% 0.75/0.95  thf('3', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(t30_waybel_9, axiom,
% 0.75/0.95    (![A:$i]:
% 0.75/0.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.75/0.95         ( v8_pre_topc @ A ) & ( v1_compts_1 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.95       ( ![B:$i]:
% 0.75/0.95         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.75/0.95             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.75/0.95           ( ?[C:$i]:
% 0.75/0.95             ( ( r3_waybel_9 @ A @ B @ C ) & 
% 0.75/0.95               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.75/0.95  thf('4', plain,
% 0.75/0.95      (![X18 : $i, X19 : $i]:
% 0.75/0.95         ((v2_struct_0 @ X18)
% 0.75/0.95          | ~ (v4_orders_2 @ X18)
% 0.75/0.95          | ~ (v7_waybel_0 @ X18)
% 0.75/0.95          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.75/0.95          | (r3_waybel_9 @ X19 @ X18 @ (sk_C_1 @ X18 @ X19))
% 0.75/0.95          | ~ (l1_pre_topc @ X19)
% 0.75/0.95          | ~ (v1_compts_1 @ X19)
% 0.75/0.95          | ~ (v8_pre_topc @ X19)
% 0.75/0.95          | ~ (v2_pre_topc @ X19)
% 0.75/0.95          | (v2_struct_0 @ X19))),
% 0.75/0.95      inference('cnf', [status(esa)], [t30_waybel_9])).
% 0.75/0.95  thf('5', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | ~ (v2_pre_topc @ sk_A)
% 0.75/0.95        | ~ (v8_pre_topc @ sk_A)
% 0.75/0.95        | ~ (v1_compts_1 @ sk_A)
% 0.75/0.95        | ~ (l1_pre_topc @ sk_A)
% 0.75/0.95        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95        | ~ (v7_waybel_0 @ sk_B)
% 0.75/0.95        | ~ (v4_orders_2 @ sk_B)
% 0.75/0.95        | (v2_struct_0 @ sk_B))),
% 0.75/0.95      inference('sup-', [status(thm)], ['3', '4'])).
% 0.75/0.95  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('7', plain, ((v8_pre_topc @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('8', plain, ((v1_compts_1 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('9', plain, ((l1_waybel_9 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('10', plain, (![X8 : $i]: ((l1_pre_topc @ X8) | ~ (l1_waybel_9 @ X8))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.75/0.95  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.95      inference('sup-', [status(thm)], ['9', '10'])).
% 0.75/0.95  thf('12', plain, ((v7_waybel_0 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('13', plain, ((v4_orders_2 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('14', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_B))),
% 0.75/0.95      inference('demod', [status(thm)], ['5', '6', '7', '8', '11', '12', '13'])).
% 0.75/0.95  thf('15', plain, (~ (v2_struct_0 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('16', plain,
% 0.75/0.95      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('clc', [status(thm)], ['14', '15'])).
% 0.75/0.95  thf('17', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('18', plain,
% 0.75/0.95      (![X18 : $i, X19 : $i]:
% 0.75/0.95         ((v2_struct_0 @ X18)
% 0.75/0.95          | ~ (v4_orders_2 @ X18)
% 0.75/0.95          | ~ (v7_waybel_0 @ X18)
% 0.75/0.95          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.75/0.95          | (m1_subset_1 @ (sk_C_1 @ X18 @ X19) @ (u1_struct_0 @ X19))
% 0.75/0.95          | ~ (l1_pre_topc @ X19)
% 0.75/0.95          | ~ (v1_compts_1 @ X19)
% 0.75/0.95          | ~ (v8_pre_topc @ X19)
% 0.75/0.95          | ~ (v2_pre_topc @ X19)
% 0.75/0.95          | (v2_struct_0 @ X19))),
% 0.75/0.95      inference('cnf', [status(esa)], [t30_waybel_9])).
% 0.75/0.95  thf('19', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | ~ (v2_pre_topc @ sk_A)
% 0.75/0.95        | ~ (v8_pre_topc @ sk_A)
% 0.75/0.95        | ~ (v1_compts_1 @ sk_A)
% 0.75/0.95        | ~ (l1_pre_topc @ sk_A)
% 0.75/0.95        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | ~ (v7_waybel_0 @ sk_B)
% 0.75/0.95        | ~ (v4_orders_2 @ sk_B)
% 0.75/0.95        | (v2_struct_0 @ sk_B))),
% 0.75/0.95      inference('sup-', [status(thm)], ['17', '18'])).
% 0.75/0.95  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('21', plain, ((v8_pre_topc @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('22', plain, ((v1_compts_1 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.95      inference('sup-', [status(thm)], ['9', '10'])).
% 0.75/0.95  thf('24', plain, ((v7_waybel_0 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('25', plain, ((v4_orders_2 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('26', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_B))),
% 0.75/0.95      inference('demod', [status(thm)],
% 0.75/0.95                ['19', '20', '21', '22', '23', '24', '25'])).
% 0.75/0.95  thf('27', plain, (~ (v2_struct_0 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('28', plain,
% 0.75/0.95      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.75/0.95  thf('29', plain,
% 0.75/0.95      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('clc', [status(thm)], ['14', '15'])).
% 0.75/0.95  thf('30', plain,
% 0.75/0.95      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.75/0.95  thf(t36_waybel_9, axiom,
% 0.75/0.95    (![A:$i]:
% 0.75/0.95     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.75/0.95         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.75/0.95         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.75/0.95       ( ![B:$i]:
% 0.75/0.95         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.75/0.95           ( ![C:$i]:
% 0.75/0.95             ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 0.75/0.95                 ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 0.75/0.95               ( ( ( ![D:$i]:
% 0.75/0.95                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.75/0.95                       ( v5_pre_topc @ ( k4_waybel_1 @ A @ D ) @ A @ A ) ) ) & 
% 0.75/0.95                   ( v11_waybel_0 @ C @ A ) & ( r3_waybel_9 @ A @ C @ B ) ) =>
% 0.75/0.95                 ( ( B ) = ( k1_waybel_9 @ A @ C ) ) ) ) ) ) ) ))).
% 0.75/0.95  thf('31', plain,
% 0.75/0.95      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.75/0.95         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.75/0.95          | (m1_subset_1 @ (sk_D_2 @ X24) @ (u1_struct_0 @ X24))
% 0.75/0.95          | ~ (v11_waybel_0 @ X25 @ X24)
% 0.75/0.95          | ~ (r3_waybel_9 @ X24 @ X25 @ X23)
% 0.75/0.95          | ((X23) = (k1_waybel_9 @ X24 @ X25))
% 0.75/0.95          | ~ (l1_waybel_0 @ X25 @ X24)
% 0.75/0.95          | ~ (v7_waybel_0 @ X25)
% 0.75/0.95          | ~ (v4_orders_2 @ X25)
% 0.75/0.95          | (v2_struct_0 @ X25)
% 0.75/0.95          | ~ (l1_waybel_9 @ X24)
% 0.75/0.95          | ~ (v1_compts_1 @ X24)
% 0.75/0.95          | ~ (v2_lattice3 @ X24)
% 0.75/0.95          | ~ (v1_lattice3 @ X24)
% 0.75/0.95          | ~ (v5_orders_2 @ X24)
% 0.75/0.95          | ~ (v4_orders_2 @ X24)
% 0.75/0.95          | ~ (v3_orders_2 @ X24)
% 0.75/0.95          | ~ (v8_pre_topc @ X24)
% 0.75/0.95          | ~ (v2_pre_topc @ X24))),
% 0.75/0.95      inference('cnf', [status(esa)], [t36_waybel_9])).
% 0.75/0.95  thf('32', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((v2_struct_0 @ sk_A)
% 0.75/0.95          | ~ (v2_pre_topc @ sk_A)
% 0.75/0.95          | ~ (v8_pre_topc @ sk_A)
% 0.75/0.95          | ~ (v3_orders_2 @ sk_A)
% 0.75/0.95          | ~ (v4_orders_2 @ sk_A)
% 0.75/0.95          | ~ (v5_orders_2 @ sk_A)
% 0.75/0.95          | ~ (v1_lattice3 @ sk_A)
% 0.75/0.95          | ~ (v2_lattice3 @ sk_A)
% 0.75/0.95          | ~ (v1_compts_1 @ sk_A)
% 0.75/0.95          | ~ (l1_waybel_9 @ sk_A)
% 0.75/0.95          | (v2_struct_0 @ X0)
% 0.75/0.95          | ~ (v4_orders_2 @ X0)
% 0.75/0.95          | ~ (v7_waybel_0 @ X0)
% 0.75/0.95          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.75/0.95          | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 0.75/0.95          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.75/0.95          | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['30', '31'])).
% 0.75/0.95  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('34', plain, ((v8_pre_topc @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('35', plain, ((v3_orders_2 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('36', plain, ((v4_orders_2 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('37', plain, ((v5_orders_2 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('38', plain, ((v1_lattice3 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('39', plain, ((v2_lattice3 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('40', plain, ((v1_compts_1 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('41', plain, ((l1_waybel_9 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('42', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((v2_struct_0 @ sk_A)
% 0.75/0.95          | (v2_struct_0 @ X0)
% 0.75/0.95          | ~ (v4_orders_2 @ X0)
% 0.75/0.95          | ~ (v7_waybel_0 @ X0)
% 0.75/0.95          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.75/0.95          | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 0.75/0.95          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.75/0.95          | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.75/0.95      inference('demod', [status(thm)],
% 0.75/0.95                ['32', '33', '34', '35', '36', '37', '38', '39', '40', '41'])).
% 0.75/0.95  thf('43', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | ~ (v11_waybel_0 @ sk_B @ sk_A)
% 0.75/0.95        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.75/0.95        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.75/0.95        | ~ (v7_waybel_0 @ sk_B)
% 0.75/0.95        | ~ (v4_orders_2 @ sk_B)
% 0.75/0.95        | (v2_struct_0 @ sk_B)
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('sup-', [status(thm)], ['29', '42'])).
% 0.75/0.95  thf('44', plain, ((v11_waybel_0 @ sk_B @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('45', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('46', plain, ((v7_waybel_0 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('47', plain, ((v4_orders_2 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('48', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.75/0.95        | (v2_struct_0 @ sk_B)
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.75/0.95  thf('49', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_B)
% 0.75/0.95        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.75/0.95        | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('simplify', [status(thm)], ['48'])).
% 0.75/0.95  thf('50', plain,
% 0.75/0.95      (![X26 : $i]:
% 0.75/0.95         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X26) @ sk_A @ sk_A)
% 0.75/0.95          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('51', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.75/0.95        | (v2_struct_0 @ sk_B)
% 0.75/0.95        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_D_2 @ sk_A)) @ sk_A @ sk_A))),
% 0.75/0.95      inference('sup-', [status(thm)], ['49', '50'])).
% 0.75/0.95  thf('52', plain,
% 0.75/0.95      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.75/0.95         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.75/0.95          | ~ (v5_pre_topc @ (k4_waybel_1 @ X24 @ (sk_D_2 @ X24)) @ X24 @ X24)
% 0.75/0.95          | ~ (v11_waybel_0 @ X25 @ X24)
% 0.75/0.95          | ~ (r3_waybel_9 @ X24 @ X25 @ X23)
% 0.75/0.95          | ((X23) = (k1_waybel_9 @ X24 @ X25))
% 0.75/0.95          | ~ (l1_waybel_0 @ X25 @ X24)
% 0.75/0.95          | ~ (v7_waybel_0 @ X25)
% 0.75/0.95          | ~ (v4_orders_2 @ X25)
% 0.75/0.95          | (v2_struct_0 @ X25)
% 0.75/0.95          | ~ (l1_waybel_9 @ X24)
% 0.75/0.95          | ~ (v1_compts_1 @ X24)
% 0.75/0.95          | ~ (v2_lattice3 @ X24)
% 0.75/0.95          | ~ (v1_lattice3 @ X24)
% 0.75/0.95          | ~ (v5_orders_2 @ X24)
% 0.75/0.95          | ~ (v4_orders_2 @ X24)
% 0.75/0.95          | ~ (v3_orders_2 @ X24)
% 0.75/0.95          | ~ (v8_pre_topc @ X24)
% 0.75/0.95          | ~ (v2_pre_topc @ X24))),
% 0.75/0.95      inference('cnf', [status(esa)], [t36_waybel_9])).
% 0.75/0.95  thf('53', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((v2_struct_0 @ sk_B)
% 0.75/0.95          | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.75/0.95          | (v2_struct_0 @ sk_A)
% 0.75/0.95          | ~ (v2_pre_topc @ sk_A)
% 0.75/0.95          | ~ (v8_pre_topc @ sk_A)
% 0.75/0.95          | ~ (v3_orders_2 @ sk_A)
% 0.75/0.95          | ~ (v4_orders_2 @ sk_A)
% 0.75/0.95          | ~ (v5_orders_2 @ sk_A)
% 0.75/0.95          | ~ (v1_lattice3 @ sk_A)
% 0.75/0.95          | ~ (v2_lattice3 @ sk_A)
% 0.75/0.95          | ~ (v1_compts_1 @ sk_A)
% 0.75/0.95          | ~ (l1_waybel_9 @ sk_A)
% 0.75/0.95          | (v2_struct_0 @ X0)
% 0.75/0.95          | ~ (v4_orders_2 @ X0)
% 0.75/0.95          | ~ (v7_waybel_0 @ X0)
% 0.75/0.95          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.75/0.95          | ((X1) = (k1_waybel_9 @ sk_A @ X0))
% 0.75/0.95          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 0.75/0.95          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.75/0.95          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['51', '52'])).
% 0.75/0.95  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('55', plain, ((v8_pre_topc @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('56', plain, ((v3_orders_2 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('57', plain, ((v4_orders_2 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('58', plain, ((v5_orders_2 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('59', plain, ((v1_lattice3 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('60', plain, ((v2_lattice3 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('61', plain, ((v1_compts_1 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('62', plain, ((l1_waybel_9 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('63', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((v2_struct_0 @ sk_B)
% 0.75/0.95          | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.75/0.95          | (v2_struct_0 @ sk_A)
% 0.75/0.95          | (v2_struct_0 @ X0)
% 0.75/0.95          | ~ (v4_orders_2 @ X0)
% 0.75/0.95          | ~ (v7_waybel_0 @ X0)
% 0.75/0.95          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.75/0.95          | ((X1) = (k1_waybel_9 @ sk_A @ X0))
% 0.75/0.95          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 0.75/0.95          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.75/0.95          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.75/0.95      inference('demod', [status(thm)],
% 0.75/0.95                ['53', '54', '55', '56', '57', '58', '59', '60', '61', '62'])).
% 0.75/0.95  thf('64', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((v2_struct_0 @ sk_A)
% 0.75/0.95          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.75/0.95          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95          | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 0.75/0.95          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.75/0.95          | ~ (v7_waybel_0 @ X0)
% 0.75/0.95          | ~ (v4_orders_2 @ X0)
% 0.75/0.95          | (v2_struct_0 @ X0)
% 0.75/0.95          | (v2_struct_0 @ sk_A)
% 0.75/0.95          | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.75/0.95          | (v2_struct_0 @ sk_B))),
% 0.75/0.95      inference('sup-', [status(thm)], ['28', '63'])).
% 0.75/0.95  thf('65', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((v2_struct_0 @ sk_B)
% 0.75/0.95          | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.75/0.95          | (v2_struct_0 @ X0)
% 0.75/0.95          | ~ (v4_orders_2 @ X0)
% 0.75/0.95          | ~ (v7_waybel_0 @ X0)
% 0.75/0.95          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.75/0.95          | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 0.75/0.95          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.75/0.95          | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('simplify', [status(thm)], ['64'])).
% 0.75/0.95  thf('66', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | (v2_struct_0 @ sk_A)
% 0.75/0.95        | ~ (v11_waybel_0 @ sk_B @ sk_A)
% 0.75/0.95        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.75/0.95        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.75/0.95        | ~ (v7_waybel_0 @ sk_B)
% 0.75/0.95        | ~ (v4_orders_2 @ sk_B)
% 0.75/0.95        | (v2_struct_0 @ sk_B)
% 0.75/0.95        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.75/0.95        | (v2_struct_0 @ sk_B))),
% 0.75/0.95      inference('sup-', [status(thm)], ['16', '65'])).
% 0.75/0.95  thf('67', plain, ((v11_waybel_0 @ sk_B @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('68', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('69', plain, ((v7_waybel_0 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('70', plain, ((v4_orders_2 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('71', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | (v2_struct_0 @ sk_A)
% 0.75/0.95        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.75/0.95        | (v2_struct_0 @ sk_B)
% 0.75/0.95        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.75/0.95        | (v2_struct_0 @ sk_B))),
% 0.75/0.95      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 0.75/0.95  thf('72', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_B)
% 0.75/0.95        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('simplify', [status(thm)], ['71'])).
% 0.75/0.95  thf('73', plain, (~ (v2_struct_0 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('74', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('clc', [status(thm)], ['72', '73'])).
% 0.75/0.95  thf('75', plain,
% 0.75/0.95      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.75/0.95  thf('76', plain,
% 0.75/0.95      (((m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A)
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('sup+', [status(thm)], ['74', '75'])).
% 0.75/0.95  thf('77', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['76'])).
% 0.75/0.95  thf('78', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('clc', [status(thm)], ['72', '73'])).
% 0.75/0.95  thf('79', plain,
% 0.75/0.95      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('clc', [status(thm)], ['14', '15'])).
% 0.75/0.95  thf('80', plain,
% 0.75/0.95      (((r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_9 @ sk_A @ sk_B))
% 0.75/0.95        | (v2_struct_0 @ sk_A)
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('sup+', [status(thm)], ['78', '79'])).
% 0.75/0.95  thf('81', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['80'])).
% 0.75/0.95  thf('82', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['76'])).
% 0.75/0.95  thf('83', plain, (![X8 : $i]: ((l1_orders_2 @ X8) | ~ (l1_waybel_9 @ X8))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.75/0.95  thf('84', plain, (![X8 : $i]: ((l1_orders_2 @ X8) | ~ (l1_waybel_9 @ X8))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.75/0.95  thf('85', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['76'])).
% 0.75/0.95  thf('86', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('clc', [status(thm)], ['72', '73'])).
% 0.75/0.95  thf('87', plain,
% 0.75/0.95      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('clc', [status(thm)], ['14', '15'])).
% 0.75/0.95  thf('88', plain,
% 0.75/0.95      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.75/0.95  thf(l51_waybel_9, axiom,
% 0.75/0.95    (![A:$i]:
% 0.75/0.95     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.75/0.95         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.75/0.95         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.75/0.95       ( ![B:$i]:
% 0.75/0.95         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.75/0.95             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.75/0.95           ( ![C:$i]:
% 0.75/0.95             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.75/0.95               ( ![D:$i]:
% 0.75/0.95                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.75/0.95                   ( ( ( ( C ) = ( D ) ) & 
% 0.75/0.95                       ( ![E:$i]:
% 0.75/0.95                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.75/0.95                           ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) ) ) & 
% 0.75/0.95                       ( v11_waybel_0 @ B @ A ) & ( r3_waybel_9 @ A @ B @ C ) ) =>
% 0.75/0.95                     ( r1_lattice3 @
% 0.75/0.95                       A @ 
% 0.75/0.95                       ( k2_relset_1 @
% 0.75/0.95                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.75/0.95                         ( u1_waybel_0 @ A @ B ) ) @ 
% 0.75/0.95                       D ) ) ) ) ) ) ) ) ))).
% 0.75/0.95  thf('89', plain,
% 0.75/0.95      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.75/0.95         ((v2_struct_0 @ X9)
% 0.75/0.95          | ~ (v4_orders_2 @ X9)
% 0.75/0.95          | ~ (v7_waybel_0 @ X9)
% 0.75/0.95          | ~ (l1_waybel_0 @ X9 @ X10)
% 0.75/0.95          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.75/0.95          | (r1_lattice3 @ X10 @ 
% 0.75/0.95             (k2_relset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X10) @ 
% 0.75/0.95              (u1_waybel_0 @ X10 @ X9)) @ 
% 0.75/0.95             X11)
% 0.75/0.95          | ((X12) != (X11))
% 0.75/0.95          | ~ (r3_waybel_9 @ X10 @ X9 @ X12)
% 0.75/0.95          | ~ (v11_waybel_0 @ X9 @ X10)
% 0.75/0.95          | (m1_subset_1 @ (sk_E @ X10) @ (u1_struct_0 @ X10))
% 0.75/0.95          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.75/0.95          | ~ (l1_waybel_9 @ X10)
% 0.75/0.95          | ~ (v1_compts_1 @ X10)
% 0.75/0.95          | ~ (v2_lattice3 @ X10)
% 0.75/0.95          | ~ (v1_lattice3 @ X10)
% 0.75/0.95          | ~ (v5_orders_2 @ X10)
% 0.75/0.95          | ~ (v4_orders_2 @ X10)
% 0.75/0.95          | ~ (v3_orders_2 @ X10)
% 0.75/0.95          | ~ (v8_pre_topc @ X10)
% 0.75/0.95          | ~ (v2_pre_topc @ X10))),
% 0.75/0.95      inference('cnf', [status(esa)], [l51_waybel_9])).
% 0.75/0.95  thf('90', plain,
% 0.75/0.95      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.75/0.95         (~ (v2_pre_topc @ X10)
% 0.75/0.95          | ~ (v8_pre_topc @ X10)
% 0.75/0.95          | ~ (v3_orders_2 @ X10)
% 0.75/0.95          | ~ (v4_orders_2 @ X10)
% 0.75/0.95          | ~ (v5_orders_2 @ X10)
% 0.75/0.95          | ~ (v1_lattice3 @ X10)
% 0.75/0.95          | ~ (v2_lattice3 @ X10)
% 0.75/0.95          | ~ (v1_compts_1 @ X10)
% 0.75/0.95          | ~ (l1_waybel_9 @ X10)
% 0.75/0.95          | (m1_subset_1 @ (sk_E @ X10) @ (u1_struct_0 @ X10))
% 0.75/0.95          | ~ (v11_waybel_0 @ X9 @ X10)
% 0.75/0.95          | ~ (r3_waybel_9 @ X10 @ X9 @ X11)
% 0.75/0.95          | (r1_lattice3 @ X10 @ 
% 0.75/0.95             (k2_relset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X10) @ 
% 0.75/0.95              (u1_waybel_0 @ X10 @ X9)) @ 
% 0.75/0.95             X11)
% 0.75/0.95          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.75/0.95          | ~ (l1_waybel_0 @ X9 @ X10)
% 0.75/0.95          | ~ (v7_waybel_0 @ X9)
% 0.75/0.95          | ~ (v4_orders_2 @ X9)
% 0.75/0.95          | (v2_struct_0 @ X9))),
% 0.75/0.95      inference('simplify', [status(thm)], ['89'])).
% 0.75/0.95  thf('91', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((v2_struct_0 @ sk_A)
% 0.75/0.95          | (v2_struct_0 @ X0)
% 0.75/0.95          | ~ (v4_orders_2 @ X0)
% 0.75/0.95          | ~ (v7_waybel_0 @ X0)
% 0.75/0.95          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.75/0.95          | (r1_lattice3 @ sk_A @ 
% 0.75/0.95             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95              (u1_waybel_0 @ sk_A @ X0)) @ 
% 0.75/0.95             (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.75/0.95          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95          | ~ (l1_waybel_9 @ sk_A)
% 0.75/0.95          | ~ (v1_compts_1 @ sk_A)
% 0.75/0.95          | ~ (v2_lattice3 @ sk_A)
% 0.75/0.95          | ~ (v1_lattice3 @ sk_A)
% 0.75/0.95          | ~ (v5_orders_2 @ sk_A)
% 0.75/0.95          | ~ (v4_orders_2 @ sk_A)
% 0.75/0.95          | ~ (v3_orders_2 @ sk_A)
% 0.75/0.95          | ~ (v8_pre_topc @ sk_A)
% 0.75/0.95          | ~ (v2_pre_topc @ sk_A))),
% 0.75/0.95      inference('sup-', [status(thm)], ['88', '90'])).
% 0.75/0.95  thf('92', plain, ((l1_waybel_9 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('93', plain, ((v1_compts_1 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('94', plain, ((v2_lattice3 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('95', plain, ((v1_lattice3 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('96', plain, ((v5_orders_2 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('97', plain, ((v4_orders_2 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('98', plain, ((v3_orders_2 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('99', plain, ((v8_pre_topc @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('101', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((v2_struct_0 @ sk_A)
% 0.75/0.95          | (v2_struct_0 @ X0)
% 0.75/0.95          | ~ (v4_orders_2 @ X0)
% 0.75/0.95          | ~ (v7_waybel_0 @ X0)
% 0.75/0.95          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.75/0.95          | (r1_lattice3 @ sk_A @ 
% 0.75/0.95             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95              (u1_waybel_0 @ sk_A @ X0)) @ 
% 0.75/0.95             (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.75/0.95          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.75/0.95      inference('demod', [status(thm)],
% 0.75/0.95                ['91', '92', '93', '94', '95', '96', '97', '98', '99', '100'])).
% 0.75/0.95  thf('102', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | ~ (v11_waybel_0 @ sk_B @ sk_A)
% 0.75/0.95        | (r1_lattice3 @ sk_A @ 
% 0.75/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95           (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.75/0.95        | ~ (v7_waybel_0 @ sk_B)
% 0.75/0.95        | ~ (v4_orders_2 @ sk_B)
% 0.75/0.95        | (v2_struct_0 @ sk_B)
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('sup-', [status(thm)], ['87', '101'])).
% 0.75/0.95  thf('103', plain, ((v11_waybel_0 @ sk_B @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('104', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('105', plain, ((v7_waybel_0 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('106', plain, ((v4_orders_2 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('107', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (r1_lattice3 @ sk_A @ 
% 0.75/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95           (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_B)
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['102', '103', '104', '105', '106'])).
% 0.75/0.95  thf('108', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_B)
% 0.75/0.95        | (r1_lattice3 @ sk_A @ 
% 0.75/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95           (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('simplify', [status(thm)], ['107'])).
% 0.75/0.95  thf('109', plain,
% 0.75/0.95      (((r1_lattice3 @ sk_A @ 
% 0.75/0.95         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95         (k1_waybel_9 @ sk_A @ sk_B))
% 0.75/0.95        | (v2_struct_0 @ sk_A)
% 0.75/0.95        | (v2_struct_0 @ sk_A)
% 0.75/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_B))),
% 0.75/0.95      inference('sup+', [status(thm)], ['86', '108'])).
% 0.75/0.95  thf('110', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_B)
% 0.75/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A)
% 0.75/0.95        | (r1_lattice3 @ sk_A @ 
% 0.75/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95           (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['109'])).
% 0.75/0.95  thf('111', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['76'])).
% 0.75/0.95  thf('112', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['80'])).
% 0.75/0.95  thf('113', plain, (![X8 : $i]: ((l1_orders_2 @ X8) | ~ (l1_waybel_9 @ X8))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.75/0.95  thf('114', plain, (![X8 : $i]: ((l1_orders_2 @ X8) | ~ (l1_waybel_9 @ X8))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.75/0.95  thf('115', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['76'])).
% 0.75/0.95  thf('116', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_B)
% 0.75/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A)
% 0.75/0.95        | (r1_lattice3 @ sk_A @ 
% 0.75/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95           (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['109'])).
% 0.75/0.95  thf('117', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['76'])).
% 0.75/0.95  thf('118', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['80'])).
% 0.75/0.95  thf('119', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('clc', [status(thm)], ['72', '73'])).
% 0.75/0.95  thf('120', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_B)
% 0.75/0.95        | (r1_lattice3 @ sk_A @ 
% 0.75/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95           (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('simplify', [status(thm)], ['107'])).
% 0.75/0.95  thf('121', plain, (![X8 : $i]: ((l1_orders_2 @ X8) | ~ (l1_waybel_9 @ X8))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.75/0.95  thf('122', plain,
% 0.75/0.95      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.75/0.95  thf(t16_yellow_0, axiom,
% 0.75/0.95    (![A:$i]:
% 0.75/0.95     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.75/0.95       ( ![B:$i]:
% 0.75/0.95         ( ( r2_yellow_0 @ A @ B ) <=>
% 0.75/0.95           ( ?[C:$i]:
% 0.75/0.95             ( ( ![D:$i]:
% 0.75/0.95                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.75/0.95                   ( ( r1_lattice3 @ A @ B @ D ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) & 
% 0.75/0.95               ( r1_lattice3 @ A @ B @ C ) & 
% 0.75/0.95               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.75/0.95  thf('123', plain,
% 0.75/0.95      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.75/0.95         ((m1_subset_1 @ (sk_D @ X1 @ X2 @ X3) @ (u1_struct_0 @ X3))
% 0.75/0.95          | ~ (r1_lattice3 @ X3 @ X2 @ X1)
% 0.75/0.95          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X3))
% 0.75/0.95          | (r2_yellow_0 @ X3 @ X2)
% 0.75/0.95          | ~ (l1_orders_2 @ X3)
% 0.75/0.95          | ~ (v5_orders_2 @ X3))),
% 0.75/0.95      inference('cnf', [status(esa)], [t16_yellow_0])).
% 0.75/0.95  thf('124', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((v2_struct_0 @ sk_A)
% 0.75/0.95          | ~ (v5_orders_2 @ sk_A)
% 0.75/0.95          | ~ (l1_orders_2 @ sk_A)
% 0.75/0.95          | (r2_yellow_0 @ sk_A @ X0)
% 0.75/0.95          | ~ (r1_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95          | (m1_subset_1 @ (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ X0 @ sk_A) @ 
% 0.75/0.95             (u1_struct_0 @ sk_A)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['122', '123'])).
% 0.75/0.95  thf('125', plain, ((v5_orders_2 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('126', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((v2_struct_0 @ sk_A)
% 0.75/0.95          | ~ (l1_orders_2 @ sk_A)
% 0.75/0.95          | (r2_yellow_0 @ sk_A @ X0)
% 0.75/0.95          | ~ (r1_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95          | (m1_subset_1 @ (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ X0 @ sk_A) @ 
% 0.75/0.95             (u1_struct_0 @ sk_A)))),
% 0.75/0.95      inference('demod', [status(thm)], ['124', '125'])).
% 0.75/0.95  thf('127', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (~ (l1_waybel_9 @ sk_A)
% 0.75/0.95          | (m1_subset_1 @ (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ X0 @ sk_A) @ 
% 0.75/0.95             (u1_struct_0 @ sk_A))
% 0.75/0.95          | ~ (r1_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95          | (r2_yellow_0 @ sk_A @ X0)
% 0.75/0.95          | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('sup-', [status(thm)], ['121', '126'])).
% 0.75/0.95  thf('128', plain, ((l1_waybel_9 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('129', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((m1_subset_1 @ (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ X0 @ sk_A) @ 
% 0.75/0.95           (u1_struct_0 @ sk_A))
% 0.75/0.95          | ~ (r1_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95          | (r2_yellow_0 @ sk_A @ X0)
% 0.75/0.95          | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['127', '128'])).
% 0.75/0.95  thf('130', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_B)
% 0.75/0.95        | (v2_struct_0 @ sk_A)
% 0.75/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.75/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.75/0.95        | (m1_subset_1 @ 
% 0.75/0.95           (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.75/0.95            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95            sk_A) @ 
% 0.75/0.95           (u1_struct_0 @ sk_A)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['120', '129'])).
% 0.75/0.95  thf('131', plain,
% 0.75/0.95      (((m1_subset_1 @ 
% 0.75/0.95         (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.75/0.95          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95          sk_A) @ 
% 0.75/0.95         (u1_struct_0 @ sk_A))
% 0.75/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.75/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.75/0.95        | (v2_struct_0 @ sk_B)
% 0.75/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('simplify', [status(thm)], ['130'])).
% 0.75/0.95  thf('132', plain,
% 0.75/0.95      (((m1_subset_1 @ 
% 0.75/0.95         (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.75/0.95          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95          sk_A) @ 
% 0.75/0.95         (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A)
% 0.75/0.95        | (v2_struct_0 @ sk_A)
% 0.75/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_B)
% 0.75/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.75/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95            (u1_waybel_0 @ sk_A @ sk_B))))),
% 0.75/0.95      inference('sup+', [status(thm)], ['119', '131'])).
% 0.75/0.95  thf('133', plain,
% 0.75/0.95      (((r2_yellow_0 @ sk_A @ 
% 0.75/0.95         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95          (u1_waybel_0 @ sk_A @ sk_B)))
% 0.75/0.95        | (v2_struct_0 @ sk_B)
% 0.75/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A)
% 0.75/0.95        | (m1_subset_1 @ 
% 0.75/0.95           (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.75/0.95            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95            sk_A) @ 
% 0.75/0.95           (u1_struct_0 @ sk_A)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['132'])).
% 0.75/0.95  thf('134', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.75/0.95      inference('clc', [status(thm)], ['72', '73'])).
% 0.75/0.95  thf('135', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_B)
% 0.75/0.95        | (r1_lattice3 @ sk_A @ 
% 0.75/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95           (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('simplify', [status(thm)], ['107'])).
% 0.75/0.95  thf('136', plain, (![X8 : $i]: ((l1_orders_2 @ X8) | ~ (l1_waybel_9 @ X8))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.75/0.95  thf('137', plain,
% 0.75/0.95      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('clc', [status(thm)], ['26', '27'])).
% 0.75/0.95  thf('138', plain,
% 0.75/0.95      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.75/0.95         ((r1_lattice3 @ X3 @ X2 @ (sk_D @ X1 @ X2 @ X3))
% 0.75/0.95          | ~ (r1_lattice3 @ X3 @ X2 @ X1)
% 0.75/0.95          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X3))
% 0.75/0.95          | (r2_yellow_0 @ X3 @ X2)
% 0.75/0.95          | ~ (l1_orders_2 @ X3)
% 0.75/0.95          | ~ (v5_orders_2 @ X3))),
% 0.75/0.95      inference('cnf', [status(esa)], [t16_yellow_0])).
% 0.75/0.95  thf('139', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((v2_struct_0 @ sk_A)
% 0.75/0.95          | ~ (v5_orders_2 @ sk_A)
% 0.75/0.95          | ~ (l1_orders_2 @ sk_A)
% 0.75/0.95          | (r2_yellow_0 @ sk_A @ X0)
% 0.75/0.95          | ~ (r1_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95          | (r1_lattice3 @ sk_A @ X0 @ 
% 0.75/0.95             (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ X0 @ sk_A)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['137', '138'])).
% 0.75/0.95  thf('140', plain, ((v5_orders_2 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('141', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((v2_struct_0 @ sk_A)
% 0.75/0.95          | ~ (l1_orders_2 @ sk_A)
% 0.75/0.95          | (r2_yellow_0 @ sk_A @ X0)
% 0.75/0.95          | ~ (r1_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95          | (r1_lattice3 @ sk_A @ X0 @ 
% 0.75/0.95             (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ X0 @ sk_A)))),
% 0.75/0.95      inference('demod', [status(thm)], ['139', '140'])).
% 0.75/0.95  thf('142', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (~ (l1_waybel_9 @ sk_A)
% 0.75/0.95          | (r1_lattice3 @ sk_A @ X0 @ 
% 0.75/0.95             (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ X0 @ sk_A))
% 0.75/0.95          | ~ (r1_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95          | (r2_yellow_0 @ sk_A @ X0)
% 0.75/0.95          | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('sup-', [status(thm)], ['136', '141'])).
% 0.75/0.95  thf('143', plain, ((l1_waybel_9 @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('144', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((r1_lattice3 @ sk_A @ X0 @ 
% 0.75/0.95           (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ X0 @ sk_A))
% 0.75/0.95          | ~ (r1_lattice3 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.75/0.95          | (r2_yellow_0 @ sk_A @ X0)
% 0.75/0.95          | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['142', '143'])).
% 0.75/0.95  thf('145', plain,
% 0.75/0.95      (((v2_struct_0 @ sk_A)
% 0.75/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_B)
% 0.75/0.95        | (v2_struct_0 @ sk_A)
% 0.75/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.75/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.75/0.95        | (r1_lattice3 @ sk_A @ 
% 0.75/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95           (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.75/0.95            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95            sk_A)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['135', '144'])).
% 0.75/0.95  thf('146', plain,
% 0.75/0.95      (((r1_lattice3 @ sk_A @ 
% 0.75/0.95         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95         (sk_D @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.75/0.95          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95          sk_A))
% 0.75/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.75/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.75/0.95        | (v2_struct_0 @ sk_B)
% 0.75/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A))),
% 0.75/0.95      inference('simplify', [status(thm)], ['145'])).
% 0.75/0.95  thf('147', plain,
% 0.75/0.95      (((r1_lattice3 @ sk_A @ 
% 0.75/0.95         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95         (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.75/0.95          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95          sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A)
% 0.75/0.95        | (v2_struct_0 @ sk_A)
% 0.75/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_B)
% 0.75/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.75/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95            (u1_waybel_0 @ sk_A @ sk_B))))),
% 0.75/0.95      inference('sup+', [status(thm)], ['134', '146'])).
% 0.75/0.95  thf('148', plain,
% 0.75/0.95      (((r2_yellow_0 @ sk_A @ 
% 0.75/0.95         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95          (u1_waybel_0 @ sk_A @ sk_B)))
% 0.75/0.95        | (v2_struct_0 @ sk_B)
% 0.75/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.75/0.95        | (v2_struct_0 @ sk_A)
% 0.75/0.95        | (r1_lattice3 @ sk_A @ 
% 0.75/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95           (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.75/0.95            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.95             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.75/0.95            sk_A)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['147'])).
% 0.75/0.95  thf(l52_waybel_9, axiom,
% 0.75/0.95    (![A:$i]:
% 0.75/0.95     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 0.75/0.95         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 0.75/0.95         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 0.75/0.95       ( ![B:$i]:
% 0.75/0.95         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.75/0.95             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.75/0.95           ( ![C:$i]:
% 0.75/0.95             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.75/0.95               ( ![D:$i]:
% 0.75/0.95                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.75/0.95                   ( ( ( ( C ) = ( D ) ) & 
% 0.75/0.95                       ( ![E:$i]:
% 0.75/0.95                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.75/0.95                           ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) ) ) & 
% 0.75/0.95                       ( r3_waybel_9 @ A @ B @ C ) ) =>
% 0.75/0.95                     ( ![E:$i]:
% 0.75/0.95                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.75/0.95                         ( ( r1_lattice3 @
% 0.75/0.95                             A @ 
% 0.75/0.95                             ( k2_relset_1 @
% 0.75/0.95                               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.75/0.95                               ( u1_waybel_0 @ A @ B ) ) @ 
% 0.75/0.95                             E ) =>
% 0.75/0.95                           ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.75/0.95  thf('149', plain,
% 0.75/0.95      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.75/0.95         ((v2_struct_0 @ X13)
% 0.75/0.95          | ~ (v4_orders_2 @ X13)
% 0.75/0.95          | ~ (v7_waybel_0 @ X13)
% 0.75/0.95          | ~ (l1_waybel_0 @ X13 @ X14)
% 0.75/0.95          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.75/0.95          | ~ (r1_lattice3 @ X14 @ 
% 0.75/0.95               (k2_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X14) @ 
% 0.75/0.95                (u1_waybel_0 @ X14 @ X13)) @ 
% 0.75/0.95               X16)
% 0.75/0.95          | (r1_orders_2 @ X14 @ X16 @ X15)
% 0.75/0.95          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.75/0.95          | ((X17) != (X15))
% 0.78/0.95          | ~ (r3_waybel_9 @ X14 @ X13 @ X17)
% 0.78/0.95          | (m1_subset_1 @ (sk_E_1 @ X14) @ (u1_struct_0 @ X14))
% 0.78/0.95          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 0.78/0.95          | ~ (l1_waybel_9 @ X14)
% 0.78/0.95          | ~ (v1_compts_1 @ X14)
% 0.78/0.95          | ~ (v2_lattice3 @ X14)
% 0.78/0.95          | ~ (v1_lattice3 @ X14)
% 0.78/0.95          | ~ (v5_orders_2 @ X14)
% 0.78/0.95          | ~ (v4_orders_2 @ X14)
% 0.78/0.95          | ~ (v3_orders_2 @ X14)
% 0.78/0.95          | ~ (v8_pre_topc @ X14)
% 0.78/0.95          | ~ (v2_pre_topc @ X14))),
% 0.78/0.95      inference('cnf', [status(esa)], [l52_waybel_9])).
% 0.78/0.95  thf('150', plain,
% 0.78/0.95      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.78/0.95         (~ (v2_pre_topc @ X14)
% 0.78/0.95          | ~ (v8_pre_topc @ X14)
% 0.78/0.95          | ~ (v3_orders_2 @ X14)
% 0.78/0.95          | ~ (v4_orders_2 @ X14)
% 0.78/0.95          | ~ (v5_orders_2 @ X14)
% 0.78/0.95          | ~ (v1_lattice3 @ X14)
% 0.78/0.95          | ~ (v2_lattice3 @ X14)
% 0.78/0.95          | ~ (v1_compts_1 @ X14)
% 0.78/0.95          | ~ (l1_waybel_9 @ X14)
% 0.78/0.95          | (m1_subset_1 @ (sk_E_1 @ X14) @ (u1_struct_0 @ X14))
% 0.78/0.95          | ~ (r3_waybel_9 @ X14 @ X13 @ X15)
% 0.78/0.95          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.78/0.95          | (r1_orders_2 @ X14 @ X16 @ X15)
% 0.78/0.95          | ~ (r1_lattice3 @ X14 @ 
% 0.78/0.95               (k2_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X14) @ 
% 0.78/0.95                (u1_waybel_0 @ X14 @ X13)) @ 
% 0.78/0.95               X16)
% 0.78/0.95          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.78/0.95          | ~ (l1_waybel_0 @ X13 @ X14)
% 0.78/0.95          | ~ (v7_waybel_0 @ X13)
% 0.78/0.95          | ~ (v4_orders_2 @ X13)
% 0.78/0.95          | (v2_struct_0 @ X13))),
% 0.78/0.95      inference('simplify', [status(thm)], ['149'])).
% 0.78/0.95  thf('151', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         ((v2_struct_0 @ sk_A)
% 0.78/0.95          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | ~ (v4_orders_2 @ sk_B)
% 0.78/0.95          | ~ (v7_waybel_0 @ sk_B)
% 0.78/0.95          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.78/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (r1_orders_2 @ sk_A @ 
% 0.78/0.95             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95              sk_A) @ 
% 0.78/0.95             X0)
% 0.78/0.95          | ~ (m1_subset_1 @ 
% 0.78/0.95               (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95                sk_A) @ 
% 0.78/0.95               (u1_struct_0 @ sk_A))
% 0.78/0.95          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.95          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | ~ (l1_waybel_9 @ sk_A)
% 0.78/0.95          | ~ (v1_compts_1 @ sk_A)
% 0.78/0.95          | ~ (v2_lattice3 @ sk_A)
% 0.78/0.95          | ~ (v1_lattice3 @ sk_A)
% 0.78/0.95          | ~ (v5_orders_2 @ sk_A)
% 0.78/0.95          | ~ (v4_orders_2 @ sk_A)
% 0.78/0.95          | ~ (v3_orders_2 @ sk_A)
% 0.78/0.95          | ~ (v8_pre_topc @ sk_A)
% 0.78/0.95          | ~ (v2_pre_topc @ sk_A))),
% 0.78/0.95      inference('sup-', [status(thm)], ['148', '150'])).
% 0.78/0.95  thf('152', plain, ((v4_orders_2 @ sk_B)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('153', plain, ((v7_waybel_0 @ sk_B)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('154', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('155', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('156', plain, ((v1_compts_1 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('157', plain, ((v2_lattice3 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('158', plain, ((v1_lattice3 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('159', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('160', plain, ((v4_orders_2 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('161', plain, ((v3_orders_2 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('162', plain, ((v8_pre_topc @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('163', plain, ((v2_pre_topc @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('164', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         ((v2_struct_0 @ sk_A)
% 0.78/0.95          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (r1_orders_2 @ sk_A @ 
% 0.78/0.95             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95              sk_A) @ 
% 0.78/0.95             X0)
% 0.78/0.95          | ~ (m1_subset_1 @ 
% 0.78/0.95               (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95                sk_A) @ 
% 0.78/0.95               (u1_struct_0 @ sk_A))
% 0.78/0.95          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.95          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.95      inference('demod', [status(thm)],
% 0.78/0.95                ['151', '152', '153', '154', '155', '156', '157', '158', 
% 0.78/0.95                 '159', '160', '161', '162', '163'])).
% 0.78/0.95  thf('165', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         ((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.95          | ~ (m1_subset_1 @ 
% 0.78/0.95               (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95                sk_A) @ 
% 0.78/0.95               (u1_struct_0 @ sk_A))
% 0.78/0.95          | (r1_orders_2 @ sk_A @ 
% 0.78/0.95             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95              sk_A) @ 
% 0.78/0.95             X0)
% 0.78/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (v2_struct_0 @ sk_A))),
% 0.78/0.95      inference('simplify', [status(thm)], ['164'])).
% 0.78/0.95  thf('166', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         ((v2_struct_0 @ sk_A)
% 0.78/0.95          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95          | (v2_struct_0 @ sk_A)
% 0.78/0.95          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (r1_orders_2 @ sk_A @ 
% 0.78/0.95             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95              sk_A) @ 
% 0.78/0.95             X0)
% 0.78/0.95          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.95          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['133', '165'])).
% 0.78/0.95  thf('167', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         ((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.95          | (r1_orders_2 @ sk_A @ 
% 0.78/0.95             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95              sk_A) @ 
% 0.78/0.95             X0)
% 0.78/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (v2_struct_0 @ sk_A))),
% 0.78/0.95      inference('simplify', [status(thm)], ['166'])).
% 0.78/0.95  thf('168', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_A)
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (r1_orders_2 @ sk_A @ 
% 0.78/0.95           (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95            sk_A) @ 
% 0.78/0.95           (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.95        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['118', '167'])).
% 0.78/0.95  thf('169', plain,
% 0.78/0.95      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (r1_orders_2 @ sk_A @ 
% 0.78/0.95           (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95            sk_A) @ 
% 0.78/0.95           (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.95        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_A))),
% 0.78/0.95      inference('simplify', [status(thm)], ['168'])).
% 0.78/0.95  thf('170', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_A)
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (r1_orders_2 @ sk_A @ 
% 0.78/0.95           (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95            sk_A) @ 
% 0.78/0.95           (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.95        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['117', '169'])).
% 0.78/0.95  thf('171', plain,
% 0.78/0.95      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (r1_orders_2 @ sk_A @ 
% 0.78/0.95           (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95            sk_A) @ 
% 0.78/0.95           (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_A))),
% 0.78/0.95      inference('simplify', [status(thm)], ['170'])).
% 0.78/0.95  thf('172', plain,
% 0.78/0.95      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.78/0.95         (~ (r1_orders_2 @ X3 @ (sk_D @ X1 @ X2 @ X3) @ X1)
% 0.78/0.95          | ~ (r1_lattice3 @ X3 @ X2 @ X1)
% 0.78/0.95          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X3))
% 0.78/0.95          | (r2_yellow_0 @ X3 @ X2)
% 0.78/0.95          | ~ (l1_orders_2 @ X3)
% 0.78/0.95          | ~ (v5_orders_2 @ X3))),
% 0.78/0.95      inference('cnf', [status(esa)], [t16_yellow_0])).
% 0.78/0.95  thf('173', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | ~ (v5_orders_2 @ sk_A)
% 0.78/0.95        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | ~ (r1_lattice3 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95             (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['171', '172'])).
% 0.78/0.95  thf('174', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('175', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | ~ (r1_lattice3 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95             (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.95      inference('demod', [status(thm)], ['173', '174'])).
% 0.78/0.95  thf('176', plain,
% 0.78/0.95      ((~ (r1_lattice3 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95           (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.95        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_A))),
% 0.78/0.95      inference('simplify', [status(thm)], ['175'])).
% 0.78/0.95  thf('177', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.95        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['116', '176'])).
% 0.78/0.95  thf('178', plain,
% 0.78/0.95      ((~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_A))),
% 0.78/0.95      inference('simplify', [status(thm)], ['177'])).
% 0.78/0.95  thf('179', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_A)
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | ~ (l1_orders_2 @ sk_A))),
% 0.78/0.95      inference('sup-', [status(thm)], ['115', '178'])).
% 0.78/0.95  thf('180', plain,
% 0.78/0.95      ((~ (l1_orders_2 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_A))),
% 0.78/0.95      inference('simplify', [status(thm)], ['179'])).
% 0.78/0.95  thf('181', plain,
% 0.78/0.95      ((~ (l1_waybel_9 @ sk_A)
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['114', '180'])).
% 0.78/0.95  thf('182', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('183', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.95      inference('demod', [status(thm)], ['181', '182'])).
% 0.78/0.95  thf(d4_waybel_9, axiom,
% 0.78/0.95    (![A:$i]:
% 0.78/0.95     ( ( l1_orders_2 @ A ) =>
% 0.78/0.95       ( ![B:$i]:
% 0.78/0.95         ( ( l1_waybel_0 @ B @ A ) =>
% 0.78/0.95           ( ( r2_waybel_9 @ A @ B ) <=>
% 0.78/0.95             ( r2_yellow_0 @
% 0.78/0.95               A @ 
% 0.78/0.95               ( k2_relset_1 @
% 0.78/0.95                 ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.78/0.95                 ( u1_waybel_0 @ A @ B ) ) ) ) ) ) ))).
% 0.78/0.95  thf('184', plain,
% 0.78/0.95      (![X6 : $i, X7 : $i]:
% 0.78/0.95         (~ (l1_waybel_0 @ X6 @ X7)
% 0.78/0.95          | ~ (r2_yellow_0 @ X7 @ 
% 0.78/0.95               (k2_relset_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X7) @ 
% 0.78/0.95                (u1_waybel_0 @ X7 @ X6)))
% 0.78/0.95          | (r2_waybel_9 @ X7 @ X6)
% 0.78/0.95          | ~ (l1_orders_2 @ X7))),
% 0.78/0.95      inference('cnf', [status(esa)], [d4_waybel_9])).
% 0.78/0.95  thf('185', plain,
% 0.78/0.95      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.78/0.95      inference('sup-', [status(thm)], ['183', '184'])).
% 0.78/0.95  thf('186', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('187', plain,
% 0.78/0.95      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B))),
% 0.78/0.95      inference('demod', [status(thm)], ['185', '186'])).
% 0.78/0.95  thf('188', plain,
% 0.78/0.95      ((~ (l1_waybel_9 @ sk_A)
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['113', '187'])).
% 0.78/0.95  thf('189', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('190', plain,
% 0.78/0.95      (((r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.95      inference('demod', [status(thm)], ['188', '189'])).
% 0.78/0.95  thf('191', plain,
% 0.78/0.95      (![X26 : $i]:
% 0.78/0.95         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X26) @ sk_A @ sk_A)
% 0.78/0.95          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('192', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A))),
% 0.78/0.95      inference('sup-', [status(thm)], ['190', '191'])).
% 0.78/0.95  thf('193', plain,
% 0.78/0.95      (((r2_yellow_0 @ sk_A @ 
% 0.78/0.95         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95          (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ 
% 0.78/0.95           (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95            sk_A) @ 
% 0.78/0.95           (u1_struct_0 @ sk_A)))),
% 0.78/0.95      inference('simplify', [status(thm)], ['132'])).
% 0.78/0.95  thf('194', plain,
% 0.78/0.95      (((r2_yellow_0 @ sk_A @ 
% 0.78/0.95         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95          (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | (r1_lattice3 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95           (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95            sk_A)))),
% 0.78/0.95      inference('simplify', [status(thm)], ['147'])).
% 0.78/0.95  thf('195', plain,
% 0.78/0.95      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.78/0.95         ((v2_struct_0 @ X13)
% 0.78/0.95          | ~ (v4_orders_2 @ X13)
% 0.78/0.95          | ~ (v7_waybel_0 @ X13)
% 0.78/0.95          | ~ (l1_waybel_0 @ X13 @ X14)
% 0.78/0.95          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.78/0.95          | ~ (r1_lattice3 @ X14 @ 
% 0.78/0.95               (k2_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X14) @ 
% 0.78/0.95                (u1_waybel_0 @ X14 @ X13)) @ 
% 0.78/0.95               X16)
% 0.78/0.95          | (r1_orders_2 @ X14 @ X16 @ X15)
% 0.78/0.95          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.78/0.95          | ((X17) != (X15))
% 0.78/0.95          | ~ (r3_waybel_9 @ X14 @ X13 @ X17)
% 0.78/0.95          | ~ (v5_pre_topc @ (k4_waybel_1 @ X14 @ (sk_E_1 @ X14)) @ X14 @ X14)
% 0.78/0.95          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X14))
% 0.78/0.95          | ~ (l1_waybel_9 @ X14)
% 0.78/0.95          | ~ (v1_compts_1 @ X14)
% 0.78/0.95          | ~ (v2_lattice3 @ X14)
% 0.78/0.95          | ~ (v1_lattice3 @ X14)
% 0.78/0.95          | ~ (v5_orders_2 @ X14)
% 0.78/0.95          | ~ (v4_orders_2 @ X14)
% 0.78/0.95          | ~ (v3_orders_2 @ X14)
% 0.78/0.95          | ~ (v8_pre_topc @ X14)
% 0.78/0.95          | ~ (v2_pre_topc @ X14))),
% 0.78/0.95      inference('cnf', [status(esa)], [l52_waybel_9])).
% 0.78/0.95  thf('196', plain,
% 0.78/0.95      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.78/0.95         (~ (v2_pre_topc @ X14)
% 0.78/0.95          | ~ (v8_pre_topc @ X14)
% 0.78/0.95          | ~ (v3_orders_2 @ X14)
% 0.78/0.95          | ~ (v4_orders_2 @ X14)
% 0.78/0.95          | ~ (v5_orders_2 @ X14)
% 0.78/0.95          | ~ (v1_lattice3 @ X14)
% 0.78/0.95          | ~ (v2_lattice3 @ X14)
% 0.78/0.95          | ~ (v1_compts_1 @ X14)
% 0.78/0.95          | ~ (l1_waybel_9 @ X14)
% 0.78/0.95          | ~ (v5_pre_topc @ (k4_waybel_1 @ X14 @ (sk_E_1 @ X14)) @ X14 @ X14)
% 0.78/0.95          | ~ (r3_waybel_9 @ X14 @ X13 @ X15)
% 0.78/0.95          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.78/0.95          | (r1_orders_2 @ X14 @ X16 @ X15)
% 0.78/0.95          | ~ (r1_lattice3 @ X14 @ 
% 0.78/0.95               (k2_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X14) @ 
% 0.78/0.95                (u1_waybel_0 @ X14 @ X13)) @ 
% 0.78/0.95               X16)
% 0.78/0.95          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.78/0.95          | ~ (l1_waybel_0 @ X13 @ X14)
% 0.78/0.95          | ~ (v7_waybel_0 @ X13)
% 0.78/0.95          | ~ (v4_orders_2 @ X13)
% 0.78/0.95          | (v2_struct_0 @ X13))),
% 0.78/0.95      inference('simplify', [status(thm)], ['195'])).
% 0.78/0.95  thf('197', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         ((v2_struct_0 @ sk_A)
% 0.78/0.95          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | ~ (v4_orders_2 @ sk_B)
% 0.78/0.95          | ~ (v7_waybel_0 @ sk_B)
% 0.78/0.95          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.78/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (r1_orders_2 @ sk_A @ 
% 0.78/0.95             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95              sk_A) @ 
% 0.78/0.95             X0)
% 0.78/0.95          | ~ (m1_subset_1 @ 
% 0.78/0.95               (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95                sk_A) @ 
% 0.78/0.95               (u1_struct_0 @ sk_A))
% 0.78/0.95          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.95          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 0.78/0.95               sk_A)
% 0.78/0.95          | ~ (l1_waybel_9 @ sk_A)
% 0.78/0.95          | ~ (v1_compts_1 @ sk_A)
% 0.78/0.95          | ~ (v2_lattice3 @ sk_A)
% 0.78/0.95          | ~ (v1_lattice3 @ sk_A)
% 0.78/0.95          | ~ (v5_orders_2 @ sk_A)
% 0.78/0.95          | ~ (v4_orders_2 @ sk_A)
% 0.78/0.95          | ~ (v3_orders_2 @ sk_A)
% 0.78/0.95          | ~ (v8_pre_topc @ sk_A)
% 0.78/0.95          | ~ (v2_pre_topc @ sk_A))),
% 0.78/0.95      inference('sup-', [status(thm)], ['194', '196'])).
% 0.78/0.95  thf('198', plain, ((v4_orders_2 @ sk_B)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('199', plain, ((v7_waybel_0 @ sk_B)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('200', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('201', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('202', plain, ((v1_compts_1 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('203', plain, ((v2_lattice3 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('204', plain, ((v1_lattice3 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('205', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('206', plain, ((v4_orders_2 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('207', plain, ((v3_orders_2 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('208', plain, ((v8_pre_topc @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('209', plain, ((v2_pre_topc @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('210', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         ((v2_struct_0 @ sk_A)
% 0.78/0.95          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (r1_orders_2 @ sk_A @ 
% 0.78/0.95             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95              sk_A) @ 
% 0.78/0.95             X0)
% 0.78/0.95          | ~ (m1_subset_1 @ 
% 0.78/0.95               (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95                sk_A) @ 
% 0.78/0.95               (u1_struct_0 @ sk_A))
% 0.78/0.95          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.95          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 0.78/0.95               sk_A))),
% 0.78/0.95      inference('demod', [status(thm)],
% 0.78/0.95                ['197', '198', '199', '200', '201', '202', '203', '204', 
% 0.78/0.95                 '205', '206', '207', '208', '209'])).
% 0.78/0.95  thf('211', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 0.78/0.95          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.95          | ~ (m1_subset_1 @ 
% 0.78/0.95               (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95                sk_A) @ 
% 0.78/0.95               (u1_struct_0 @ sk_A))
% 0.78/0.95          | (r1_orders_2 @ sk_A @ 
% 0.78/0.95             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95              sk_A) @ 
% 0.78/0.95             X0)
% 0.78/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (v2_struct_0 @ sk_A))),
% 0.78/0.95      inference('simplify', [status(thm)], ['210'])).
% 0.78/0.95  thf('212', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         ((v2_struct_0 @ sk_A)
% 0.78/0.95          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95          | (v2_struct_0 @ sk_A)
% 0.78/0.95          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (r1_orders_2 @ sk_A @ 
% 0.78/0.95             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95              sk_A) @ 
% 0.78/0.95             X0)
% 0.78/0.95          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.95          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 0.78/0.95               sk_A))),
% 0.78/0.95      inference('sup-', [status(thm)], ['193', '211'])).
% 0.78/0.95  thf('213', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 0.78/0.95          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.95          | (r1_orders_2 @ sk_A @ 
% 0.78/0.95             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95              sk_A) @ 
% 0.78/0.95             X0)
% 0.78/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (v2_struct_0 @ sk_A))),
% 0.78/0.95      inference('simplify', [status(thm)], ['212'])).
% 0.78/0.95  thf('214', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         ((r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95          | (v2_struct_0 @ sk_A)
% 0.78/0.95          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | (v2_struct_0 @ sk_A)
% 0.78/0.95          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (r1_orders_2 @ sk_A @ 
% 0.78/0.95             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95              sk_A) @ 
% 0.78/0.95             X0)
% 0.78/0.95          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0))),
% 0.78/0.95      inference('sup-', [status(thm)], ['192', '213'])).
% 0.78/0.95  thf('215', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         (~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.95          | (r1_orders_2 @ sk_A @ 
% 0.78/0.95             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95              sk_A) @ 
% 0.78/0.95             X0)
% 0.78/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (v2_struct_0 @ sk_A)
% 0.78/0.95          | (r2_waybel_9 @ sk_A @ sk_B))),
% 0.78/0.95      inference('simplify', [status(thm)], ['214'])).
% 0.78/0.95  thf('216', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_A)
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (r1_orders_2 @ sk_A @ 
% 0.78/0.95           (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95            sk_A) @ 
% 0.78/0.95           (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['112', '215'])).
% 0.78/0.95  thf('217', plain,
% 0.78/0.95      (((r1_orders_2 @ sk_A @ 
% 0.78/0.95         (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95          sk_A) @ 
% 0.78/0.95         (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.95        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (v2_struct_0 @ sk_A))),
% 0.78/0.95      inference('simplify', [status(thm)], ['216'])).
% 0.78/0.95  thf('218', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_A)
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (r1_orders_2 @ sk_A @ 
% 0.78/0.95           (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95            sk_A) @ 
% 0.78/0.95           (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['111', '217'])).
% 0.78/0.95  thf('219', plain,
% 0.78/0.95      (((r1_orders_2 @ sk_A @ 
% 0.78/0.95         (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.95          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95          sk_A) @ 
% 0.78/0.95         (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (v2_struct_0 @ sk_A))),
% 0.78/0.95      inference('simplify', [status(thm)], ['218'])).
% 0.78/0.95  thf('220', plain,
% 0.78/0.95      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.78/0.95         (~ (r1_orders_2 @ X3 @ (sk_D @ X1 @ X2 @ X3) @ X1)
% 0.78/0.95          | ~ (r1_lattice3 @ X3 @ X2 @ X1)
% 0.78/0.95          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X3))
% 0.78/0.95          | (r2_yellow_0 @ X3 @ X2)
% 0.78/0.95          | ~ (l1_orders_2 @ X3)
% 0.78/0.95          | ~ (v5_orders_2 @ X3))),
% 0.78/0.95      inference('cnf', [status(esa)], [t16_yellow_0])).
% 0.78/0.95  thf('221', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_A)
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | ~ (v5_orders_2 @ sk_A)
% 0.78/0.95        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | ~ (r1_lattice3 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95             (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['219', '220'])).
% 0.78/0.95  thf('222', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('223', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_A)
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | ~ (r1_lattice3 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95             (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.95      inference('demod', [status(thm)], ['221', '222'])).
% 0.78/0.95  thf('224', plain,
% 0.78/0.95      ((~ (r1_lattice3 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95           (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.95        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (v2_struct_0 @ sk_A))),
% 0.78/0.95      inference('simplify', [status(thm)], ['223'])).
% 0.78/0.95  thf('225', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.95        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['110', '224'])).
% 0.78/0.95  thf('226', plain,
% 0.78/0.95      ((~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_A))),
% 0.78/0.95      inference('simplify', [status(thm)], ['225'])).
% 0.78/0.95  thf('227', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_A)
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | ~ (l1_orders_2 @ sk_A))),
% 0.78/0.95      inference('sup-', [status(thm)], ['85', '226'])).
% 0.78/0.95  thf('228', plain,
% 0.78/0.95      ((~ (l1_orders_2 @ sk_A)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_A))),
% 0.78/0.95      inference('simplify', [status(thm)], ['227'])).
% 0.78/0.95  thf('229', plain,
% 0.78/0.95      ((~ (l1_waybel_9 @ sk_A)
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B))))),
% 0.78/0.95      inference('sup-', [status(thm)], ['84', '228'])).
% 0.78/0.95  thf('230', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('231', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B))))),
% 0.78/0.95      inference('demod', [status(thm)], ['229', '230'])).
% 0.78/0.95  thf('232', plain,
% 0.78/0.95      (![X6 : $i, X7 : $i]:
% 0.78/0.95         (~ (l1_waybel_0 @ X6 @ X7)
% 0.78/0.95          | ~ (r2_yellow_0 @ X7 @ 
% 0.78/0.95               (k2_relset_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X7) @ 
% 0.78/0.95                (u1_waybel_0 @ X7 @ X6)))
% 0.78/0.95          | (r2_waybel_9 @ X7 @ X6)
% 0.78/0.95          | ~ (l1_orders_2 @ X7))),
% 0.78/0.95      inference('cnf', [status(esa)], [d4_waybel_9])).
% 0.78/0.95  thf('233', plain,
% 0.78/0.95      (((r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.78/0.95      inference('sup-', [status(thm)], ['231', '232'])).
% 0.78/0.95  thf('234', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('235', plain,
% 0.78/0.95      (((r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B))),
% 0.78/0.95      inference('demod', [status(thm)], ['233', '234'])).
% 0.78/0.95  thf('236', plain,
% 0.78/0.95      ((~ (l1_orders_2 @ sk_A)
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B))),
% 0.78/0.95      inference('simplify', [status(thm)], ['235'])).
% 0.78/0.95  thf('237', plain,
% 0.78/0.95      ((~ (l1_waybel_9 @ sk_A)
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_A))),
% 0.78/0.95      inference('sup-', [status(thm)], ['83', '236'])).
% 0.78/0.95  thf('238', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('239', plain,
% 0.78/0.95      (((r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.95        | (v2_struct_0 @ sk_A))),
% 0.78/0.95      inference('demod', [status(thm)], ['237', '238'])).
% 0.78/0.95  thf('240', plain,
% 0.78/0.95      (![X26 : $i]:
% 0.78/0.95         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X26) @ sk_A @ sk_A)
% 0.78/0.95          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('241', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_A)
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E @ sk_A)) @ sk_A @ sk_A))),
% 0.78/0.95      inference('sup-', [status(thm)], ['239', '240'])).
% 0.78/0.95  thf('242', plain,
% 0.78/0.95      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.78/0.95         ((v2_struct_0 @ X9)
% 0.78/0.95          | ~ (v4_orders_2 @ X9)
% 0.78/0.95          | ~ (v7_waybel_0 @ X9)
% 0.78/0.95          | ~ (l1_waybel_0 @ X9 @ X10)
% 0.78/0.95          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.78/0.95          | (r1_lattice3 @ X10 @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X10) @ 
% 0.78/0.95              (u1_waybel_0 @ X10 @ X9)) @ 
% 0.78/0.95             X11)
% 0.78/0.95          | ((X12) != (X11))
% 0.78/0.95          | ~ (r3_waybel_9 @ X10 @ X9 @ X12)
% 0.78/0.95          | ~ (v11_waybel_0 @ X9 @ X10)
% 0.78/0.95          | ~ (v5_pre_topc @ (k4_waybel_1 @ X10 @ (sk_E @ X10)) @ X10 @ X10)
% 0.78/0.95          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.78/0.95          | ~ (l1_waybel_9 @ X10)
% 0.78/0.95          | ~ (v1_compts_1 @ X10)
% 0.78/0.95          | ~ (v2_lattice3 @ X10)
% 0.78/0.95          | ~ (v1_lattice3 @ X10)
% 0.78/0.95          | ~ (v5_orders_2 @ X10)
% 0.78/0.95          | ~ (v4_orders_2 @ X10)
% 0.78/0.95          | ~ (v3_orders_2 @ X10)
% 0.78/0.95          | ~ (v8_pre_topc @ X10)
% 0.78/0.95          | ~ (v2_pre_topc @ X10))),
% 0.78/0.95      inference('cnf', [status(esa)], [l51_waybel_9])).
% 0.78/0.95  thf('243', plain,
% 0.78/0.95      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.78/0.95         (~ (v2_pre_topc @ X10)
% 0.78/0.95          | ~ (v8_pre_topc @ X10)
% 0.78/0.95          | ~ (v3_orders_2 @ X10)
% 0.78/0.95          | ~ (v4_orders_2 @ X10)
% 0.78/0.95          | ~ (v5_orders_2 @ X10)
% 0.78/0.95          | ~ (v1_lattice3 @ X10)
% 0.78/0.95          | ~ (v2_lattice3 @ X10)
% 0.78/0.95          | ~ (v1_compts_1 @ X10)
% 0.78/0.95          | ~ (l1_waybel_9 @ X10)
% 0.78/0.95          | ~ (v5_pre_topc @ (k4_waybel_1 @ X10 @ (sk_E @ X10)) @ X10 @ X10)
% 0.78/0.95          | ~ (v11_waybel_0 @ X9 @ X10)
% 0.78/0.95          | ~ (r3_waybel_9 @ X10 @ X9 @ X11)
% 0.78/0.95          | (r1_lattice3 @ X10 @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X10) @ 
% 0.78/0.95              (u1_waybel_0 @ X10 @ X9)) @ 
% 0.78/0.95             X11)
% 0.78/0.95          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.78/0.95          | ~ (l1_waybel_0 @ X9 @ X10)
% 0.78/0.95          | ~ (v7_waybel_0 @ X9)
% 0.78/0.95          | ~ (v4_orders_2 @ X9)
% 0.78/0.95          | (v2_struct_0 @ X9))),
% 0.78/0.95      inference('simplify', [status(thm)], ['242'])).
% 0.78/0.95  thf('244', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i]:
% 0.78/0.95         ((r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | (v2_struct_0 @ sk_A)
% 0.78/0.95          | (v2_struct_0 @ X0)
% 0.78/0.95          | ~ (v4_orders_2 @ X0)
% 0.78/0.95          | ~ (v7_waybel_0 @ X0)
% 0.78/0.95          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.95          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (r1_lattice3 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ X0)) @ 
% 0.78/0.95             X1)
% 0.78/0.95          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 0.78/0.95          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.78/0.95          | ~ (l1_waybel_9 @ sk_A)
% 0.78/0.95          | ~ (v1_compts_1 @ sk_A)
% 0.78/0.95          | ~ (v2_lattice3 @ sk_A)
% 0.78/0.95          | ~ (v1_lattice3 @ sk_A)
% 0.78/0.95          | ~ (v5_orders_2 @ sk_A)
% 0.78/0.95          | ~ (v4_orders_2 @ sk_A)
% 0.78/0.95          | ~ (v3_orders_2 @ sk_A)
% 0.78/0.95          | ~ (v8_pre_topc @ sk_A)
% 0.78/0.95          | ~ (v2_pre_topc @ sk_A))),
% 0.78/0.95      inference('sup-', [status(thm)], ['241', '243'])).
% 0.78/0.95  thf('245', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('246', plain, ((v1_compts_1 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('247', plain, ((v2_lattice3 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('248', plain, ((v1_lattice3 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('249', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('250', plain, ((v4_orders_2 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('251', plain, ((v3_orders_2 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('252', plain, ((v8_pre_topc @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('253', plain, ((v2_pre_topc @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('254', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i]:
% 0.78/0.95         ((r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | (v2_struct_0 @ sk_A)
% 0.78/0.95          | (v2_struct_0 @ X0)
% 0.78/0.95          | ~ (v4_orders_2 @ X0)
% 0.78/0.95          | ~ (v7_waybel_0 @ X0)
% 0.78/0.95          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.95          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.78/0.95          | (r1_lattice3 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ X0)) @ 
% 0.78/0.95             X1)
% 0.78/0.95          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 0.78/0.95          | ~ (v11_waybel_0 @ X0 @ sk_A))),
% 0.78/0.95      inference('demod', [status(thm)],
% 0.78/0.95                ['244', '245', '246', '247', '248', '249', '250', '251', 
% 0.78/0.95                 '252', '253'])).
% 0.78/0.95  thf('255', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         ((v2_struct_0 @ sk_A)
% 0.78/0.95          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.78/0.95          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.95          | (r1_lattice3 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ X0)) @ 
% 0.78/0.95             (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.95          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.95          | ~ (v7_waybel_0 @ X0)
% 0.78/0.95          | ~ (v4_orders_2 @ X0)
% 0.78/0.95          | (v2_struct_0 @ X0)
% 0.78/0.95          | (v2_struct_0 @ sk_A)
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | (r2_waybel_9 @ sk_A @ sk_B))),
% 0.78/0.95      inference('sup-', [status(thm)], ['82', '254'])).
% 0.78/0.95  thf('256', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         ((r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95          | (v2_struct_0 @ sk_B)
% 0.78/0.95          | (v2_struct_0 @ X0)
% 0.78/0.95          | ~ (v4_orders_2 @ X0)
% 0.78/0.95          | ~ (v7_waybel_0 @ X0)
% 0.78/0.95          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.95          | (r1_lattice3 @ sk_A @ 
% 0.78/0.95             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95              (u1_waybel_0 @ sk_A @ X0)) @ 
% 0.78/0.95             (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.95          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.95          | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.78/0.95          | (v2_struct_0 @ sk_A))),
% 0.78/0.95      inference('simplify', [status(thm)], ['255'])).
% 0.78/0.95  thf('257', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_A)
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | ~ (v11_waybel_0 @ sk_B @ sk_A)
% 0.78/0.95        | (r1_lattice3 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95           (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.95        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.78/0.95        | ~ (v7_waybel_0 @ sk_B)
% 0.78/0.95        | ~ (v4_orders_2 @ sk_B)
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B))),
% 0.78/0.95      inference('sup-', [status(thm)], ['81', '256'])).
% 0.78/0.95  thf('258', plain, ((v11_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('259', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('260', plain, ((v7_waybel_0 @ sk_B)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('261', plain, ((v4_orders_2 @ sk_B)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('262', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_A)
% 0.78/0.95        | (v2_struct_0 @ sk_A)
% 0.78/0.95        | (r1_lattice3 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95           (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r2_waybel_9 @ sk_A @ sk_B))),
% 0.78/0.95      inference('demod', [status(thm)], ['257', '258', '259', '260', '261'])).
% 0.78/0.95  thf('263', plain,
% 0.78/0.95      (((r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.95        | (v2_struct_0 @ sk_B)
% 0.78/0.95        | (r1_lattice3 @ sk_A @ 
% 0.78/0.95           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.95            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.95           (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.95        | (v2_struct_0 @ sk_A))),
% 0.78/0.95      inference('simplify', [status(thm)], ['262'])).
% 0.78/0.95  thf('264', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_A)
% 0.78/0.95        | (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.95      inference('simplify', [status(thm)], ['76'])).
% 0.78/0.95  thf('265', plain,
% 0.78/0.95      (((v2_struct_0 @ sk_A)
% 0.78/0.95        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.95      inference('simplify', [status(thm)], ['80'])).
% 0.78/0.95  thf('266', plain, (![X8 : $i]: ((l1_orders_2 @ X8) | ~ (l1_waybel_9 @ X8))),
% 0.78/0.96      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.78/0.96  thf('267', plain, (![X8 : $i]: ((l1_orders_2 @ X8) | ~ (l1_waybel_9 @ X8))),
% 0.78/0.96      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.78/0.96  thf('268', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('simplify', [status(thm)], ['76'])).
% 0.78/0.96  thf('269', plain,
% 0.78/0.96      (((r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r1_lattice3 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96           (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['262'])).
% 0.78/0.96  thf('270', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('simplify', [status(thm)], ['76'])).
% 0.78/0.96  thf('271', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('simplify', [status(thm)], ['80'])).
% 0.78/0.96  thf('272', plain,
% 0.78/0.96      (((r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r1_lattice3 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96           (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['262'])).
% 0.78/0.96  thf('273', plain, (![X8 : $i]: ((l1_orders_2 @ X8) | ~ (l1_waybel_9 @ X8))),
% 0.78/0.96      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.78/0.96  thf('274', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('simplify', [status(thm)], ['76'])).
% 0.78/0.96  thf('275', plain,
% 0.78/0.96      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.78/0.96         ((m1_subset_1 @ (sk_D @ X1 @ X2 @ X3) @ (u1_struct_0 @ X3))
% 0.78/0.96          | ~ (r1_lattice3 @ X3 @ X2 @ X1)
% 0.78/0.96          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X3))
% 0.78/0.96          | (r2_yellow_0 @ X3 @ X2)
% 0.78/0.96          | ~ (l1_orders_2 @ X3)
% 0.78/0.96          | ~ (v5_orders_2 @ X3))),
% 0.78/0.96      inference('cnf', [status(esa)], [t16_yellow_0])).
% 0.78/0.96  thf('276', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | ~ (v5_orders_2 @ sk_A)
% 0.78/0.96          | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ X0)
% 0.78/0.96          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96          | (m1_subset_1 @ (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_A) @ 
% 0.78/0.96             (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['274', '275'])).
% 0.78/0.96  thf('277', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('278', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ X0)
% 0.78/0.96          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96          | (m1_subset_1 @ (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_A) @ 
% 0.78/0.96             (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('demod', [status(thm)], ['276', '277'])).
% 0.78/0.96  thf('279', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         (~ (l1_waybel_9 @ sk_A)
% 0.78/0.96          | (m1_subset_1 @ (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_A) @ 
% 0.78/0.96             (u1_struct_0 @ sk_A))
% 0.78/0.96          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ X0)
% 0.78/0.96          | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['273', '278'])).
% 0.78/0.96  thf('280', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('281', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((m1_subset_1 @ (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_A) @ 
% 0.78/0.96           (u1_struct_0 @ sk_A))
% 0.78/0.96          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ X0)
% 0.78/0.96          | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('demod', [status(thm)], ['279', '280'])).
% 0.78/0.96  thf('282', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (m1_subset_1 @ 
% 0.78/0.96           (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96            sk_A) @ 
% 0.78/0.96           (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['272', '281'])).
% 0.78/0.96  thf('283', plain,
% 0.78/0.96      (((m1_subset_1 @ 
% 0.78/0.96         (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96          sk_A) @ 
% 0.78/0.96         (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['282'])).
% 0.78/0.96  thf('284', plain,
% 0.78/0.96      (((r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r1_lattice3 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96           (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['262'])).
% 0.78/0.96  thf('285', plain, (![X8 : $i]: ((l1_orders_2 @ X8) | ~ (l1_waybel_9 @ X8))),
% 0.78/0.96      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.78/0.96  thf('286', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('simplify', [status(thm)], ['76'])).
% 0.78/0.96  thf('287', plain,
% 0.78/0.96      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.78/0.96         ((r1_lattice3 @ X3 @ X2 @ (sk_D @ X1 @ X2 @ X3))
% 0.78/0.96          | ~ (r1_lattice3 @ X3 @ X2 @ X1)
% 0.78/0.96          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X3))
% 0.78/0.96          | (r2_yellow_0 @ X3 @ X2)
% 0.78/0.96          | ~ (l1_orders_2 @ X3)
% 0.78/0.96          | ~ (v5_orders_2 @ X3))),
% 0.78/0.96      inference('cnf', [status(esa)], [t16_yellow_0])).
% 0.78/0.96  thf('288', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | ~ (v5_orders_2 @ sk_A)
% 0.78/0.96          | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ X0)
% 0.78/0.96          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96          | (r1_lattice3 @ sk_A @ X0 @ 
% 0.78/0.96             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_A)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['286', '287'])).
% 0.78/0.96  thf('289', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('290', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ X0)
% 0.78/0.96          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96          | (r1_lattice3 @ sk_A @ X0 @ 
% 0.78/0.96             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_A)))),
% 0.78/0.96      inference('demod', [status(thm)], ['288', '289'])).
% 0.78/0.96  thf('291', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         (~ (l1_waybel_9 @ sk_A)
% 0.78/0.96          | (r1_lattice3 @ sk_A @ X0 @ 
% 0.78/0.96             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_A))
% 0.78/0.96          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ X0)
% 0.78/0.96          | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['285', '290'])).
% 0.78/0.96  thf('292', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('293', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((r1_lattice3 @ sk_A @ X0 @ 
% 0.78/0.96           (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ X0 @ sk_A))
% 0.78/0.96          | ~ (r1_lattice3 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ X0)
% 0.78/0.96          | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('demod', [status(thm)], ['291', '292'])).
% 0.78/0.96  thf('294', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (r1_lattice3 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96           (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96            sk_A)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['284', '293'])).
% 0.78/0.96  thf('295', plain,
% 0.78/0.96      (((r1_lattice3 @ sk_A @ 
% 0.78/0.96         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96         (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96          sk_A))
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['294'])).
% 0.78/0.96  thf('296', plain,
% 0.78/0.96      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.78/0.96         (~ (v2_pre_topc @ X14)
% 0.78/0.96          | ~ (v8_pre_topc @ X14)
% 0.78/0.96          | ~ (v3_orders_2 @ X14)
% 0.78/0.96          | ~ (v4_orders_2 @ X14)
% 0.78/0.96          | ~ (v5_orders_2 @ X14)
% 0.78/0.96          | ~ (v1_lattice3 @ X14)
% 0.78/0.96          | ~ (v2_lattice3 @ X14)
% 0.78/0.96          | ~ (v1_compts_1 @ X14)
% 0.78/0.96          | ~ (l1_waybel_9 @ X14)
% 0.78/0.96          | (m1_subset_1 @ (sk_E_1 @ X14) @ (u1_struct_0 @ X14))
% 0.78/0.96          | ~ (r3_waybel_9 @ X14 @ X13 @ X15)
% 0.78/0.96          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.78/0.96          | (r1_orders_2 @ X14 @ X16 @ X15)
% 0.78/0.96          | ~ (r1_lattice3 @ X14 @ 
% 0.78/0.96               (k2_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X14) @ 
% 0.78/0.96                (u1_waybel_0 @ X14 @ X13)) @ 
% 0.78/0.96               X16)
% 0.78/0.96          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.78/0.96          | ~ (l1_waybel_0 @ X13 @ X14)
% 0.78/0.96          | ~ (v7_waybel_0 @ X13)
% 0.78/0.96          | ~ (v4_orders_2 @ X13)
% 0.78/0.96          | (v2_struct_0 @ X13))),
% 0.78/0.96      inference('simplify', [status(thm)], ['149'])).
% 0.78/0.96  thf('297', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_B)
% 0.78/0.96          | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96          | (v2_struct_0 @ sk_B)
% 0.78/0.96          | ~ (v4_orders_2 @ sk_B)
% 0.78/0.96          | ~ (v7_waybel_0 @ sk_B)
% 0.78/0.96          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.78/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r1_orders_2 @ sk_A @ 
% 0.78/0.96             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96              sk_A) @ 
% 0.78/0.96             X0)
% 0.78/0.96          | ~ (m1_subset_1 @ 
% 0.78/0.96               (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96                sk_A) @ 
% 0.78/0.96               (u1_struct_0 @ sk_A))
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.96          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | ~ (l1_waybel_9 @ sk_A)
% 0.78/0.96          | ~ (v1_compts_1 @ sk_A)
% 0.78/0.96          | ~ (v2_lattice3 @ sk_A)
% 0.78/0.96          | ~ (v1_lattice3 @ sk_A)
% 0.78/0.96          | ~ (v5_orders_2 @ sk_A)
% 0.78/0.96          | ~ (v4_orders_2 @ sk_A)
% 0.78/0.96          | ~ (v3_orders_2 @ sk_A)
% 0.78/0.96          | ~ (v8_pre_topc @ sk_A)
% 0.78/0.96          | ~ (v2_pre_topc @ sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['295', '296'])).
% 0.78/0.96  thf('298', plain, ((v4_orders_2 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('299', plain, ((v7_waybel_0 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('300', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('301', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('302', plain, ((v1_compts_1 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('303', plain, ((v2_lattice3 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('304', plain, ((v1_lattice3 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('305', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('306', plain, ((v4_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('307', plain, ((v3_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('308', plain, ((v8_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('309', plain, ((v2_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('310', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_B)
% 0.78/0.96          | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96          | (v2_struct_0 @ sk_B)
% 0.78/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r1_orders_2 @ sk_A @ 
% 0.78/0.96             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96              sk_A) @ 
% 0.78/0.96             X0)
% 0.78/0.96          | ~ (m1_subset_1 @ 
% 0.78/0.96               (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96                sk_A) @ 
% 0.78/0.96               (u1_struct_0 @ sk_A))
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.96          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('demod', [status(thm)],
% 0.78/0.96                ['297', '298', '299', '300', '301', '302', '303', '304', 
% 0.78/0.96                 '305', '306', '307', '308', '309'])).
% 0.78/0.96  thf('311', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.96          | ~ (m1_subset_1 @ 
% 0.78/0.96               (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96                sk_A) @ 
% 0.78/0.96               (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r1_orders_2 @ sk_A @ 
% 0.78/0.96             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96              sk_A) @ 
% 0.78/0.96             X0)
% 0.78/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96          | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96          | (v2_struct_0 @ sk_B)
% 0.78/0.96          | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['310'])).
% 0.78/0.96  thf('312', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_B)
% 0.78/0.96          | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_B)
% 0.78/0.96          | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r1_orders_2 @ sk_A @ 
% 0.78/0.96             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96              sk_A) @ 
% 0.78/0.96             X0)
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.96          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['283', '311'])).
% 0.78/0.96  thf('313', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.96          | (r1_orders_2 @ sk_A @ 
% 0.78/0.96             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96              sk_A) @ 
% 0.78/0.96             X0)
% 0.78/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96          | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96          | (v2_struct_0 @ sk_B)
% 0.78/0.96          | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['312'])).
% 0.78/0.96  thf('314', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r1_orders_2 @ sk_A @ 
% 0.78/0.96           (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96            sk_A) @ 
% 0.78/0.96           (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['271', '313'])).
% 0.78/0.96  thf('315', plain,
% 0.78/0.96      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r1_orders_2 @ sk_A @ 
% 0.78/0.96           (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96            sk_A) @ 
% 0.78/0.96           (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['314'])).
% 0.78/0.96  thf('316', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (r1_orders_2 @ sk_A @ 
% 0.78/0.96           (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96            sk_A) @ 
% 0.78/0.96           (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['270', '315'])).
% 0.78/0.96  thf('317', plain,
% 0.78/0.96      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r1_orders_2 @ sk_A @ 
% 0.78/0.96           (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96            sk_A) @ 
% 0.78/0.96           (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['316'])).
% 0.78/0.96  thf('318', plain,
% 0.78/0.96      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.78/0.96         (~ (r1_orders_2 @ X3 @ (sk_D @ X1 @ X2 @ X3) @ X1)
% 0.78/0.96          | ~ (r1_lattice3 @ X3 @ X2 @ X1)
% 0.78/0.96          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X3))
% 0.78/0.96          | (r2_yellow_0 @ X3 @ X2)
% 0.78/0.96          | ~ (l1_orders_2 @ X3)
% 0.78/0.96          | ~ (v5_orders_2 @ X3))),
% 0.78/0.96      inference('cnf', [status(esa)], [t16_yellow_0])).
% 0.78/0.96  thf('319', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | ~ (v5_orders_2 @ sk_A)
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | ~ (r1_lattice3 @ sk_A @ 
% 0.78/0.96             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96             (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['317', '318'])).
% 0.78/0.96  thf('320', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('321', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | ~ (r1_lattice3 @ sk_A @ 
% 0.78/0.96             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96             (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('demod', [status(thm)], ['319', '320'])).
% 0.78/0.96  thf('322', plain,
% 0.78/0.96      ((~ (r1_lattice3 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96           (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['321'])).
% 0.78/0.96  thf('323', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['269', '322'])).
% 0.78/0.96  thf('324', plain,
% 0.78/0.96      ((~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['323'])).
% 0.78/0.96  thf('325', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['268', '324'])).
% 0.78/0.96  thf('326', plain,
% 0.78/0.96      ((~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['325'])).
% 0.78/0.96  thf('327', plain,
% 0.78/0.96      ((~ (l1_waybel_9 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['267', '326'])).
% 0.78/0.96  thf('328', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('329', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('demod', [status(thm)], ['327', '328'])).
% 0.78/0.96  thf('330', plain,
% 0.78/0.96      (![X6 : $i, X7 : $i]:
% 0.78/0.96         (~ (l1_waybel_0 @ X6 @ X7)
% 0.78/0.96          | ~ (r2_yellow_0 @ X7 @ 
% 0.78/0.96               (k2_relset_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X7) @ 
% 0.78/0.96                (u1_waybel_0 @ X7 @ X6)))
% 0.78/0.96          | (r2_waybel_9 @ X7 @ X6)
% 0.78/0.96          | ~ (l1_orders_2 @ X7))),
% 0.78/0.96      inference('cnf', [status(esa)], [d4_waybel_9])).
% 0.78/0.96  thf('331', plain,
% 0.78/0.96      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['329', '330'])).
% 0.78/0.96  thf('332', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('333', plain,
% 0.78/0.96      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B))),
% 0.78/0.96      inference('demod', [status(thm)], ['331', '332'])).
% 0.78/0.96  thf('334', plain,
% 0.78/0.96      ((~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('simplify', [status(thm)], ['333'])).
% 0.78/0.96  thf('335', plain,
% 0.78/0.96      ((~ (l1_waybel_9 @ sk_A)
% 0.78/0.96        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['266', '334'])).
% 0.78/0.96  thf('336', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('337', plain,
% 0.78/0.96      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('demod', [status(thm)], ['335', '336'])).
% 0.78/0.96  thf('338', plain,
% 0.78/0.96      (![X26 : $i]:
% 0.78/0.96         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X26) @ sk_A @ sk_A)
% 0.78/0.96          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('339', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['337', '338'])).
% 0.78/0.96  thf('340', plain,
% 0.78/0.96      (((m1_subset_1 @ 
% 0.78/0.96         (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96          sk_A) @ 
% 0.78/0.96         (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['282'])).
% 0.78/0.96  thf('341', plain,
% 0.78/0.96      (((r1_lattice3 @ sk_A @ 
% 0.78/0.96         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96         (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96          sk_A))
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['294'])).
% 0.78/0.96  thf('342', plain,
% 0.78/0.96      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.78/0.96         (~ (v2_pre_topc @ X14)
% 0.78/0.96          | ~ (v8_pre_topc @ X14)
% 0.78/0.96          | ~ (v3_orders_2 @ X14)
% 0.78/0.96          | ~ (v4_orders_2 @ X14)
% 0.78/0.96          | ~ (v5_orders_2 @ X14)
% 0.78/0.96          | ~ (v1_lattice3 @ X14)
% 0.78/0.96          | ~ (v2_lattice3 @ X14)
% 0.78/0.96          | ~ (v1_compts_1 @ X14)
% 0.78/0.96          | ~ (l1_waybel_9 @ X14)
% 0.78/0.96          | ~ (v5_pre_topc @ (k4_waybel_1 @ X14 @ (sk_E_1 @ X14)) @ X14 @ X14)
% 0.78/0.96          | ~ (r3_waybel_9 @ X14 @ X13 @ X15)
% 0.78/0.96          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.78/0.96          | (r1_orders_2 @ X14 @ X16 @ X15)
% 0.78/0.96          | ~ (r1_lattice3 @ X14 @ 
% 0.78/0.96               (k2_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X14) @ 
% 0.78/0.96                (u1_waybel_0 @ X14 @ X13)) @ 
% 0.78/0.96               X16)
% 0.78/0.96          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.78/0.96          | ~ (l1_waybel_0 @ X13 @ X14)
% 0.78/0.96          | ~ (v7_waybel_0 @ X13)
% 0.78/0.96          | ~ (v4_orders_2 @ X13)
% 0.78/0.96          | (v2_struct_0 @ X13))),
% 0.78/0.96      inference('simplify', [status(thm)], ['195'])).
% 0.78/0.96  thf('343', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_B)
% 0.78/0.96          | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96          | (v2_struct_0 @ sk_B)
% 0.78/0.96          | ~ (v4_orders_2 @ sk_B)
% 0.78/0.96          | ~ (v7_waybel_0 @ sk_B)
% 0.78/0.96          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.78/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r1_orders_2 @ sk_A @ 
% 0.78/0.96             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96              sk_A) @ 
% 0.78/0.96             X0)
% 0.78/0.96          | ~ (m1_subset_1 @ 
% 0.78/0.96               (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96                sk_A) @ 
% 0.78/0.96               (u1_struct_0 @ sk_A))
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.96          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 0.78/0.96               sk_A)
% 0.78/0.96          | ~ (l1_waybel_9 @ sk_A)
% 0.78/0.96          | ~ (v1_compts_1 @ sk_A)
% 0.78/0.96          | ~ (v2_lattice3 @ sk_A)
% 0.78/0.96          | ~ (v1_lattice3 @ sk_A)
% 0.78/0.96          | ~ (v5_orders_2 @ sk_A)
% 0.78/0.96          | ~ (v4_orders_2 @ sk_A)
% 0.78/0.96          | ~ (v3_orders_2 @ sk_A)
% 0.78/0.96          | ~ (v8_pre_topc @ sk_A)
% 0.78/0.96          | ~ (v2_pre_topc @ sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['341', '342'])).
% 0.78/0.96  thf('344', plain, ((v4_orders_2 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('345', plain, ((v7_waybel_0 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('346', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('347', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('348', plain, ((v1_compts_1 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('349', plain, ((v2_lattice3 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('350', plain, ((v1_lattice3 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('351', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('352', plain, ((v4_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('353', plain, ((v3_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('354', plain, ((v8_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('355', plain, ((v2_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('356', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_B)
% 0.78/0.96          | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96          | (v2_struct_0 @ sk_B)
% 0.78/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r1_orders_2 @ sk_A @ 
% 0.78/0.96             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96              sk_A) @ 
% 0.78/0.96             X0)
% 0.78/0.96          | ~ (m1_subset_1 @ 
% 0.78/0.96               (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96                sk_A) @ 
% 0.78/0.96               (u1_struct_0 @ sk_A))
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.96          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 0.78/0.96               sk_A))),
% 0.78/0.96      inference('demod', [status(thm)],
% 0.78/0.96                ['343', '344', '345', '346', '347', '348', '349', '350', 
% 0.78/0.96                 '351', '352', '353', '354', '355'])).
% 0.78/0.96  thf('357', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         (~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.96          | ~ (m1_subset_1 @ 
% 0.78/0.96               (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96                sk_A) @ 
% 0.78/0.96               (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r1_orders_2 @ sk_A @ 
% 0.78/0.96             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96              sk_A) @ 
% 0.78/0.96             X0)
% 0.78/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96          | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96          | (v2_struct_0 @ sk_B)
% 0.78/0.96          | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['356'])).
% 0.78/0.96  thf('358', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_B)
% 0.78/0.96          | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_B)
% 0.78/0.96          | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r1_orders_2 @ sk_A @ 
% 0.78/0.96             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96              sk_A) @ 
% 0.78/0.96             X0)
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.96          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 0.78/0.96               sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['340', '357'])).
% 0.78/0.96  thf('359', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         (~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.96          | (r1_orders_2 @ sk_A @ 
% 0.78/0.96             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96              sk_A) @ 
% 0.78/0.96             X0)
% 0.78/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96          | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96          | (v2_struct_0 @ sk_B)
% 0.78/0.96          | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['358'])).
% 0.78/0.96  thf('360', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96          | (v2_struct_0 @ sk_B)
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_B)
% 0.78/0.96          | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r1_orders_2 @ sk_A @ 
% 0.78/0.96             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96              sk_A) @ 
% 0.78/0.96             X0)
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0))),
% 0.78/0.96      inference('sup-', [status(thm)], ['339', '359'])).
% 0.78/0.96  thf('361', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         (~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 0.78/0.96          | (r1_orders_2 @ sk_A @ 
% 0.78/0.96             (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96              sk_A) @ 
% 0.78/0.96             X0)
% 0.78/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96              (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_B)
% 0.78/0.96          | (r2_waybel_9 @ sk_A @ sk_B))),
% 0.78/0.96      inference('simplify', [status(thm)], ['360'])).
% 0.78/0.96  thf('362', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r1_orders_2 @ sk_A @ 
% 0.78/0.96           (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96            sk_A) @ 
% 0.78/0.96           (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['265', '361'])).
% 0.78/0.96  thf('363', plain,
% 0.78/0.96      (((r1_orders_2 @ sk_A @ 
% 0.78/0.96         (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96          sk_A) @ 
% 0.78/0.96         (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['362'])).
% 0.78/0.96  thf('364', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (r1_orders_2 @ sk_A @ 
% 0.78/0.96           (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96            sk_A) @ 
% 0.78/0.96           (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['264', '363'])).
% 0.78/0.96  thf('365', plain,
% 0.78/0.96      (((r1_orders_2 @ sk_A @ 
% 0.78/0.96         (sk_D @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96          sk_A) @ 
% 0.78/0.96         (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['364'])).
% 0.78/0.96  thf('366', plain,
% 0.78/0.96      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.78/0.96         (~ (r1_orders_2 @ X3 @ (sk_D @ X1 @ X2 @ X3) @ X1)
% 0.78/0.96          | ~ (r1_lattice3 @ X3 @ X2 @ X1)
% 0.78/0.96          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X3))
% 0.78/0.96          | (r2_yellow_0 @ X3 @ X2)
% 0.78/0.96          | ~ (l1_orders_2 @ X3)
% 0.78/0.96          | ~ (v5_orders_2 @ X3))),
% 0.78/0.96      inference('cnf', [status(esa)], [t16_yellow_0])).
% 0.78/0.96  thf('367', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | ~ (v5_orders_2 @ sk_A)
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | ~ (r1_lattice3 @ sk_A @ 
% 0.78/0.96             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96             (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['365', '366'])).
% 0.78/0.96  thf('368', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('369', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | ~ (r1_lattice3 @ sk_A @ 
% 0.78/0.96             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96             (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('demod', [status(thm)], ['367', '368'])).
% 0.78/0.96  thf('370', plain,
% 0.78/0.96      ((~ (r1_lattice3 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 0.78/0.96           (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['369'])).
% 0.78/0.96  thf('371', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | ~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['263', '370'])).
% 0.78/0.96  thf('372', plain,
% 0.78/0.96      ((~ (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['371'])).
% 0.78/0.96  thf('373', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['77', '372'])).
% 0.78/0.96  thf('374', plain,
% 0.78/0.96      ((~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B)))
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['373'])).
% 0.78/0.96  thf('375', plain,
% 0.78/0.96      ((~ (l1_waybel_9 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['2', '374'])).
% 0.78/0.96  thf('376', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('377', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (r2_yellow_0 @ sk_A @ 
% 0.78/0.96           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.78/0.96            (u1_waybel_0 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('demod', [status(thm)], ['375', '376'])).
% 0.78/0.96  thf('378', plain,
% 0.78/0.96      (![X6 : $i, X7 : $i]:
% 0.78/0.96         (~ (l1_waybel_0 @ X6 @ X7)
% 0.78/0.96          | ~ (r2_yellow_0 @ X7 @ 
% 0.78/0.96               (k2_relset_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X7) @ 
% 0.78/0.96                (u1_waybel_0 @ X7 @ X6)))
% 0.78/0.96          | (r2_waybel_9 @ X7 @ X6)
% 0.78/0.96          | ~ (l1_orders_2 @ X7))),
% 0.78/0.96      inference('cnf', [status(esa)], [d4_waybel_9])).
% 0.78/0.96  thf('379', plain,
% 0.78/0.96      (((r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['377', '378'])).
% 0.78/0.96  thf('380', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('381', plain,
% 0.78/0.96      (((r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B))),
% 0.78/0.96      inference('demod', [status(thm)], ['379', '380'])).
% 0.78/0.96  thf('382', plain,
% 0.78/0.96      ((~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B))),
% 0.78/0.96      inference('simplify', [status(thm)], ['381'])).
% 0.78/0.96  thf('383', plain,
% 0.78/0.96      ((~ (l1_waybel_9 @ sk_A)
% 0.78/0.96        | (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['1', '382'])).
% 0.78/0.96  thf('384', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('385', plain,
% 0.78/0.96      (((r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('demod', [status(thm)], ['383', '384'])).
% 0.78/0.96  thf('386', plain,
% 0.78/0.96      ((~ (r2_waybel_9 @ sk_A @ sk_B)
% 0.78/0.96        | ~ (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96             (k10_yellow_6 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('387', plain,
% 0.78/0.96      ((~ (r2_waybel_9 @ sk_A @ sk_B)) <= (~ ((r2_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('split', [status(esa)], ['386'])).
% 0.78/0.96  thf('388', plain, (![X8 : $i]: ((l1_orders_2 @ X8) | ~ (l1_waybel_9 @ X8))),
% 0.78/0.96      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 0.78/0.96  thf('389', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('clc', [status(thm)], ['72', '73'])).
% 0.78/0.96  thf('390', plain,
% 0.78/0.96      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('clc', [status(thm)], ['14', '15'])).
% 0.78/0.96  thf('391', plain,
% 0.78/0.96      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('clc', [status(thm)], ['26', '27'])).
% 0.78/0.96  thf(t33_waybel_9, axiom,
% 0.78/0.96    (![A:$i]:
% 0.78/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.78/0.96         ( v8_pre_topc @ A ) & ( v1_compts_1 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.78/0.96       ( ![B:$i]:
% 0.78/0.96         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.78/0.96             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.78/0.96           ( ( ![C:$i]:
% 0.78/0.96               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.78/0.96                 ( ![D:$i]:
% 0.78/0.96                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.78/0.96                     ( ( ( r3_waybel_9 @ A @ B @ C ) & 
% 0.78/0.96                         ( r3_waybel_9 @ A @ B @ D ) ) =>
% 0.78/0.96                       ( ( C ) = ( D ) ) ) ) ) ) ) =>
% 0.78/0.96             ( ![C:$i]:
% 0.78/0.96               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.78/0.96                 ( ( r3_waybel_9 @ A @ B @ C ) =>
% 0.78/0.96                   ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.78/0.96  thf('392', plain,
% 0.78/0.96      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.78/0.96         ((v2_struct_0 @ X20)
% 0.78/0.96          | ~ (v4_orders_2 @ X20)
% 0.78/0.96          | ~ (v7_waybel_0 @ X20)
% 0.78/0.96          | ~ (l1_waybel_0 @ X20 @ X21)
% 0.78/0.96          | ~ (r3_waybel_9 @ X21 @ X20 @ X22)
% 0.78/0.96          | (r2_hidden @ X22 @ (k10_yellow_6 @ X21 @ X20))
% 0.78/0.96          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.78/0.96          | (r3_waybel_9 @ X21 @ X20 @ (sk_C_2 @ X20 @ X21))
% 0.78/0.96          | ~ (l1_pre_topc @ X21)
% 0.78/0.96          | ~ (v1_compts_1 @ X21)
% 0.78/0.96          | ~ (v8_pre_topc @ X21)
% 0.78/0.96          | ~ (v2_pre_topc @ X21)
% 0.78/0.96          | (v2_struct_0 @ X21))),
% 0.78/0.96      inference('cnf', [status(esa)], [t33_waybel_9])).
% 0.78/0.96  thf('393', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | ~ (v2_pre_topc @ sk_A)
% 0.78/0.96          | ~ (v8_pre_topc @ sk_A)
% 0.78/0.96          | ~ (v1_compts_1 @ sk_A)
% 0.78/0.96          | ~ (l1_pre_topc @ sk_A)
% 0.78/0.96          | (r3_waybel_9 @ sk_A @ X0 @ (sk_C_2 @ X0 @ sk_A))
% 0.78/0.96          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.78/0.96          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96          | ~ (v7_waybel_0 @ X0)
% 0.78/0.96          | ~ (v4_orders_2 @ X0)
% 0.78/0.96          | (v2_struct_0 @ X0))),
% 0.78/0.96      inference('sup-', [status(thm)], ['391', '392'])).
% 0.78/0.96  thf('394', plain, ((v2_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('395', plain, ((v8_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('396', plain, ((v1_compts_1 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('397', plain, ((l1_pre_topc @ sk_A)),
% 0.78/0.96      inference('sup-', [status(thm)], ['9', '10'])).
% 0.78/0.96  thf('398', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | (r3_waybel_9 @ sk_A @ X0 @ (sk_C_2 @ X0 @ sk_A))
% 0.78/0.96          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.78/0.96          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96          | ~ (v7_waybel_0 @ X0)
% 0.78/0.96          | ~ (v4_orders_2 @ X0)
% 0.78/0.96          | (v2_struct_0 @ X0))),
% 0.78/0.96      inference('demod', [status(thm)], ['393', '394', '395', '396', '397'])).
% 0.78/0.96  thf('399', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ X0)
% 0.78/0.96          | ~ (v4_orders_2 @ X0)
% 0.78/0.96          | ~ (v7_waybel_0 @ X0)
% 0.78/0.96          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.78/0.96          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.78/0.96          | (r3_waybel_9 @ sk_A @ X0 @ (sk_C_2 @ X0 @ sk_A))
% 0.78/0.96          | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['398'])).
% 0.78/0.96  thf('400', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_2 @ sk_B @ sk_A))
% 0.78/0.96        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.78/0.96        | ~ (v7_waybel_0 @ sk_B)
% 0.78/0.96        | ~ (v4_orders_2 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B))),
% 0.78/0.96      inference('sup-', [status(thm)], ['390', '399'])).
% 0.78/0.96  thf('401', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('402', plain, ((v7_waybel_0 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('403', plain, ((v4_orders_2 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('404', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_2 @ sk_B @ sk_A))
% 0.78/0.96        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96        | (v2_struct_0 @ sk_B))),
% 0.78/0.96      inference('demod', [status(thm)], ['400', '401', '402', '403'])).
% 0.78/0.96  thf('405', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_2 @ sk_B @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['404'])).
% 0.78/0.96  thf('406', plain,
% 0.78/0.96      (((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_2 @ sk_B @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_B))),
% 0.78/0.96      inference('sup+', [status(thm)], ['389', '405'])).
% 0.78/0.96  thf('407', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_B)
% 0.78/0.96        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_2 @ sk_B @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96           (k10_yellow_6 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('simplify', [status(thm)], ['406'])).
% 0.78/0.96  thf('408', plain,
% 0.78/0.96      ((~ (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96           (k10_yellow_6 @ sk_A @ sk_B)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('split', [status(esa)], ['386'])).
% 0.78/0.96  thf('409', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_A)
% 0.78/0.96         | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_2 @ sk_B @ sk_A))
% 0.78/0.96         | (v2_struct_0 @ sk_B)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['407', '408'])).
% 0.78/0.96  thf('410', plain, (~ (v2_struct_0 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('411', plain,
% 0.78/0.96      ((((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_2 @ sk_B @ sk_A))
% 0.78/0.96         | (v2_struct_0 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('clc', [status(thm)], ['409', '410'])).
% 0.78/0.96  thf('412', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('clc', [status(thm)], ['72', '73'])).
% 0.78/0.96  thf('413', plain,
% 0.78/0.96      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('clc', [status(thm)], ['14', '15'])).
% 0.78/0.96  thf('414', plain,
% 0.78/0.96      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('clc', [status(thm)], ['26', '27'])).
% 0.78/0.96  thf('415', plain,
% 0.78/0.96      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.78/0.96         ((v2_struct_0 @ X20)
% 0.78/0.96          | ~ (v4_orders_2 @ X20)
% 0.78/0.96          | ~ (v7_waybel_0 @ X20)
% 0.78/0.96          | ~ (l1_waybel_0 @ X20 @ X21)
% 0.78/0.96          | ~ (r3_waybel_9 @ X21 @ X20 @ X22)
% 0.78/0.96          | (r2_hidden @ X22 @ (k10_yellow_6 @ X21 @ X20))
% 0.78/0.96          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.78/0.96          | (m1_subset_1 @ (sk_C_2 @ X20 @ X21) @ (u1_struct_0 @ X21))
% 0.78/0.96          | ~ (l1_pre_topc @ X21)
% 0.78/0.96          | ~ (v1_compts_1 @ X21)
% 0.78/0.96          | ~ (v8_pre_topc @ X21)
% 0.78/0.96          | ~ (v2_pre_topc @ X21)
% 0.78/0.96          | (v2_struct_0 @ X21))),
% 0.78/0.96      inference('cnf', [status(esa)], [t33_waybel_9])).
% 0.78/0.96  thf('416', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | ~ (v2_pre_topc @ sk_A)
% 0.78/0.96          | ~ (v8_pre_topc @ sk_A)
% 0.78/0.96          | ~ (v1_compts_1 @ sk_A)
% 0.78/0.96          | ~ (l1_pre_topc @ sk_A)
% 0.78/0.96          | (m1_subset_1 @ (sk_C_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.78/0.96          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96          | ~ (v7_waybel_0 @ X0)
% 0.78/0.96          | ~ (v4_orders_2 @ X0)
% 0.78/0.96          | (v2_struct_0 @ X0))),
% 0.78/0.96      inference('sup-', [status(thm)], ['414', '415'])).
% 0.78/0.96  thf('417', plain, ((v2_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('418', plain, ((v8_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('419', plain, ((v1_compts_1 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('420', plain, ((l1_pre_topc @ sk_A)),
% 0.78/0.96      inference('sup-', [status(thm)], ['9', '10'])).
% 0.78/0.96  thf('421', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | (m1_subset_1 @ (sk_C_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.78/0.96          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96          | ~ (v7_waybel_0 @ X0)
% 0.78/0.96          | ~ (v4_orders_2 @ X0)
% 0.78/0.96          | (v2_struct_0 @ X0))),
% 0.78/0.96      inference('demod', [status(thm)], ['416', '417', '418', '419', '420'])).
% 0.78/0.96  thf('422', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ X0)
% 0.78/0.96          | ~ (v4_orders_2 @ X0)
% 0.78/0.96          | ~ (v7_waybel_0 @ X0)
% 0.78/0.96          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.78/0.96          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.78/0.96          | (m1_subset_1 @ (sk_C_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['421'])).
% 0.78/0.96  thf('423', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.78/0.96        | ~ (v7_waybel_0 @ sk_B)
% 0.78/0.96        | ~ (v4_orders_2 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B))),
% 0.78/0.96      inference('sup-', [status(thm)], ['413', '422'])).
% 0.78/0.96  thf('424', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('425', plain, ((v7_waybel_0 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('426', plain, ((v4_orders_2 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('427', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96        | (v2_struct_0 @ sk_B))),
% 0.78/0.96      inference('demod', [status(thm)], ['423', '424', '425', '426'])).
% 0.78/0.96  thf('428', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96        | (m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['427'])).
% 0.78/0.96  thf('429', plain,
% 0.78/0.96      (((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_B))),
% 0.78/0.96      inference('sup+', [status(thm)], ['412', '428'])).
% 0.78/0.96  thf('430', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_B)
% 0.78/0.96        | (m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96           (k10_yellow_6 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('simplify', [status(thm)], ['429'])).
% 0.78/0.96  thf('431', plain,
% 0.78/0.96      ((~ (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96           (k10_yellow_6 @ sk_A @ sk_B)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('split', [status(esa)], ['386'])).
% 0.78/0.96  thf('432', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_A)
% 0.78/0.96         | (m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96         | (v2_struct_0 @ sk_B)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['430', '431'])).
% 0.78/0.96  thf('433', plain, (~ (v2_struct_0 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('434', plain,
% 0.78/0.96      ((((m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96         | (v2_struct_0 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('clc', [status(thm)], ['432', '433'])).
% 0.78/0.96  thf('435', plain,
% 0.78/0.96      ((((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_2 @ sk_B @ sk_A))
% 0.78/0.96         | (v2_struct_0 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('clc', [status(thm)], ['409', '410'])).
% 0.78/0.96  thf('436', plain,
% 0.78/0.96      ((((m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96         | (v2_struct_0 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('clc', [status(thm)], ['432', '433'])).
% 0.78/0.96  thf('437', plain,
% 0.78/0.96      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.78/0.96         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.78/0.96          | (m1_subset_1 @ (sk_D_2 @ X24) @ (u1_struct_0 @ X24))
% 0.78/0.96          | ~ (v11_waybel_0 @ X25 @ X24)
% 0.78/0.96          | ~ (r3_waybel_9 @ X24 @ X25 @ X23)
% 0.78/0.96          | ((X23) = (k1_waybel_9 @ X24 @ X25))
% 0.78/0.96          | ~ (l1_waybel_0 @ X25 @ X24)
% 0.78/0.96          | ~ (v7_waybel_0 @ X25)
% 0.78/0.96          | ~ (v4_orders_2 @ X25)
% 0.78/0.96          | (v2_struct_0 @ X25)
% 0.78/0.96          | ~ (l1_waybel_9 @ X24)
% 0.78/0.96          | ~ (v1_compts_1 @ X24)
% 0.78/0.96          | ~ (v2_lattice3 @ X24)
% 0.78/0.96          | ~ (v1_lattice3 @ X24)
% 0.78/0.96          | ~ (v5_orders_2 @ X24)
% 0.78/0.96          | ~ (v4_orders_2 @ X24)
% 0.78/0.96          | ~ (v3_orders_2 @ X24)
% 0.78/0.96          | ~ (v8_pre_topc @ X24)
% 0.78/0.96          | ~ (v2_pre_topc @ X24))),
% 0.78/0.96      inference('cnf', [status(esa)], [t36_waybel_9])).
% 0.78/0.96  thf('438', plain,
% 0.78/0.96      ((![X0 : $i]:
% 0.78/0.96          ((v2_struct_0 @ sk_A)
% 0.78/0.96           | ~ (v2_pre_topc @ sk_A)
% 0.78/0.96           | ~ (v8_pre_topc @ sk_A)
% 0.78/0.96           | ~ (v3_orders_2 @ sk_A)
% 0.78/0.96           | ~ (v4_orders_2 @ sk_A)
% 0.78/0.96           | ~ (v5_orders_2 @ sk_A)
% 0.78/0.96           | ~ (v1_lattice3 @ sk_A)
% 0.78/0.96           | ~ (v2_lattice3 @ sk_A)
% 0.78/0.96           | ~ (v1_compts_1 @ sk_A)
% 0.78/0.96           | ~ (l1_waybel_9 @ sk_A)
% 0.78/0.96           | (v2_struct_0 @ X0)
% 0.78/0.96           | ~ (v4_orders_2 @ X0)
% 0.78/0.96           | ~ (v7_waybel_0 @ X0)
% 0.78/0.96           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 0.78/0.96           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_2 @ sk_B @ sk_A))
% 0.78/0.96           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['436', '437'])).
% 0.78/0.96  thf('439', plain, ((v2_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('440', plain, ((v8_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('441', plain, ((v3_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('442', plain, ((v4_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('443', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('444', plain, ((v1_lattice3 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('445', plain, ((v2_lattice3 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('446', plain, ((v1_compts_1 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('447', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('448', plain,
% 0.78/0.96      ((![X0 : $i]:
% 0.78/0.96          ((v2_struct_0 @ sk_A)
% 0.78/0.96           | (v2_struct_0 @ X0)
% 0.78/0.96           | ~ (v4_orders_2 @ X0)
% 0.78/0.96           | ~ (v7_waybel_0 @ X0)
% 0.78/0.96           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 0.78/0.96           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_2 @ sk_B @ sk_A))
% 0.78/0.96           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('demod', [status(thm)],
% 0.78/0.96                ['438', '439', '440', '441', '442', '443', '444', '445', 
% 0.78/0.96                 '446', '447'])).
% 0.78/0.96  thf('449', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_A)
% 0.78/0.96         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96         | ~ (v11_waybel_0 @ sk_B @ sk_A)
% 0.78/0.96         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.78/0.96         | ~ (v7_waybel_0 @ sk_B)
% 0.78/0.96         | ~ (v4_orders_2 @ sk_B)
% 0.78/0.96         | (v2_struct_0 @ sk_B)
% 0.78/0.96         | (v2_struct_0 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['435', '448'])).
% 0.78/0.96  thf('450', plain, ((v11_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('451', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('452', plain, ((v7_waybel_0 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('453', plain, ((v4_orders_2 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('454', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_A)
% 0.78/0.96         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | (v2_struct_0 @ sk_B)
% 0.78/0.96         | (v2_struct_0 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('demod', [status(thm)], ['449', '450', '451', '452', '453'])).
% 0.78/0.96  thf('455', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_B)
% 0.78/0.96         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96         | (v2_struct_0 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('simplify', [status(thm)], ['454'])).
% 0.78/0.96  thf('456', plain,
% 0.78/0.96      (![X26 : $i]:
% 0.78/0.96         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X26) @ sk_A @ sk_A)
% 0.78/0.96          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('457', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_A)
% 0.78/0.96         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | (v2_struct_0 @ sk_B)
% 0.78/0.96         | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_D_2 @ sk_A)) @ sk_A @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['455', '456'])).
% 0.78/0.96  thf('458', plain,
% 0.78/0.96      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.78/0.96         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.78/0.96          | ~ (v5_pre_topc @ (k4_waybel_1 @ X24 @ (sk_D_2 @ X24)) @ X24 @ X24)
% 0.78/0.96          | ~ (v11_waybel_0 @ X25 @ X24)
% 0.78/0.96          | ~ (r3_waybel_9 @ X24 @ X25 @ X23)
% 0.78/0.96          | ((X23) = (k1_waybel_9 @ X24 @ X25))
% 0.78/0.96          | ~ (l1_waybel_0 @ X25 @ X24)
% 0.78/0.96          | ~ (v7_waybel_0 @ X25)
% 0.78/0.96          | ~ (v4_orders_2 @ X25)
% 0.78/0.96          | (v2_struct_0 @ X25)
% 0.78/0.96          | ~ (l1_waybel_9 @ X24)
% 0.78/0.96          | ~ (v1_compts_1 @ X24)
% 0.78/0.96          | ~ (v2_lattice3 @ X24)
% 0.78/0.96          | ~ (v1_lattice3 @ X24)
% 0.78/0.96          | ~ (v5_orders_2 @ X24)
% 0.78/0.96          | ~ (v4_orders_2 @ X24)
% 0.78/0.96          | ~ (v3_orders_2 @ X24)
% 0.78/0.96          | ~ (v8_pre_topc @ X24)
% 0.78/0.96          | ~ (v2_pre_topc @ X24))),
% 0.78/0.96      inference('cnf', [status(esa)], [t36_waybel_9])).
% 0.78/0.96  thf('459', plain,
% 0.78/0.96      ((![X0 : $i, X1 : $i]:
% 0.78/0.96          ((v2_struct_0 @ sk_B)
% 0.78/0.96           | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96           | (v2_struct_0 @ sk_A)
% 0.78/0.96           | ~ (v2_pre_topc @ sk_A)
% 0.78/0.96           | ~ (v8_pre_topc @ sk_A)
% 0.78/0.96           | ~ (v3_orders_2 @ sk_A)
% 0.78/0.96           | ~ (v4_orders_2 @ sk_A)
% 0.78/0.96           | ~ (v5_orders_2 @ sk_A)
% 0.78/0.96           | ~ (v1_lattice3 @ sk_A)
% 0.78/0.96           | ~ (v2_lattice3 @ sk_A)
% 0.78/0.96           | ~ (v1_compts_1 @ sk_A)
% 0.78/0.96           | ~ (l1_waybel_9 @ sk_A)
% 0.78/0.96           | (v2_struct_0 @ X0)
% 0.78/0.96           | ~ (v4_orders_2 @ X0)
% 0.78/0.96           | ~ (v7_waybel_0 @ X0)
% 0.78/0.96           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | ((X1) = (k1_waybel_9 @ sk_A @ X0))
% 0.78/0.96           | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 0.78/0.96           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['457', '458'])).
% 0.78/0.96  thf('460', plain, ((v2_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('461', plain, ((v8_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('462', plain, ((v3_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('463', plain, ((v4_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('464', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('465', plain, ((v1_lattice3 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('466', plain, ((v2_lattice3 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('467', plain, ((v1_compts_1 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('468', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('469', plain,
% 0.78/0.96      ((![X0 : $i, X1 : $i]:
% 0.78/0.96          ((v2_struct_0 @ sk_B)
% 0.78/0.96           | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96           | (v2_struct_0 @ sk_A)
% 0.78/0.96           | (v2_struct_0 @ X0)
% 0.78/0.96           | ~ (v4_orders_2 @ X0)
% 0.78/0.96           | ~ (v7_waybel_0 @ X0)
% 0.78/0.96           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | ((X1) = (k1_waybel_9 @ sk_A @ X0))
% 0.78/0.96           | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 0.78/0.96           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('demod', [status(thm)],
% 0.78/0.96                ['459', '460', '461', '462', '463', '464', '465', '466', 
% 0.78/0.96                 '467', '468'])).
% 0.78/0.96  thf('470', plain,
% 0.78/0.96      ((![X0 : $i]:
% 0.78/0.96          ((v2_struct_0 @ sk_A)
% 0.78/0.96           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_2 @ sk_B @ sk_A))
% 0.78/0.96           | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 0.78/0.96           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | ~ (v7_waybel_0 @ X0)
% 0.78/0.96           | ~ (v4_orders_2 @ X0)
% 0.78/0.96           | (v2_struct_0 @ X0)
% 0.78/0.96           | (v2_struct_0 @ sk_A)
% 0.78/0.96           | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96           | (v2_struct_0 @ sk_B)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['434', '469'])).
% 0.78/0.96  thf('471', plain,
% 0.78/0.96      ((![X0 : $i]:
% 0.78/0.96          ((v2_struct_0 @ sk_B)
% 0.78/0.96           | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96           | (v2_struct_0 @ X0)
% 0.78/0.96           | ~ (v4_orders_2 @ X0)
% 0.78/0.96           | ~ (v7_waybel_0 @ X0)
% 0.78/0.96           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 0.78/0.96           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_2 @ sk_B @ sk_A))
% 0.78/0.96           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | (v2_struct_0 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('simplify', [status(thm)], ['470'])).
% 0.78/0.96  thf('472', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_A)
% 0.78/0.96         | (v2_struct_0 @ sk_A)
% 0.78/0.96         | ~ (v11_waybel_0 @ sk_B @ sk_A)
% 0.78/0.96         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.78/0.96         | ~ (v7_waybel_0 @ sk_B)
% 0.78/0.96         | ~ (v4_orders_2 @ sk_B)
% 0.78/0.96         | (v2_struct_0 @ sk_B)
% 0.78/0.96         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | (v2_struct_0 @ sk_B)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['411', '471'])).
% 0.78/0.96  thf('473', plain, ((v11_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('474', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('475', plain, ((v7_waybel_0 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('476', plain, ((v4_orders_2 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('477', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_A)
% 0.78/0.96         | (v2_struct_0 @ sk_A)
% 0.78/0.96         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | (v2_struct_0 @ sk_B)
% 0.78/0.96         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | (v2_struct_0 @ sk_B)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('demod', [status(thm)], ['472', '473', '474', '475', '476'])).
% 0.78/0.96  thf('478', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_B)
% 0.78/0.96         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | (v2_struct_0 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('simplify', [status(thm)], ['477'])).
% 0.78/0.96  thf('479', plain, (~ (v2_struct_0 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('480', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_A)
% 0.78/0.96         | ((sk_C_2 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('clc', [status(thm)], ['478', '479'])).
% 0.78/0.96  thf('481', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('clc', [status(thm)], ['72', '73'])).
% 0.78/0.96  thf('482', plain,
% 0.78/0.96      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('clc', [status(thm)], ['14', '15'])).
% 0.78/0.96  thf('483', plain,
% 0.78/0.96      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('clc', [status(thm)], ['26', '27'])).
% 0.78/0.96  thf('484', plain,
% 0.78/0.96      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.78/0.96         ((v2_struct_0 @ X20)
% 0.78/0.96          | ~ (v4_orders_2 @ X20)
% 0.78/0.96          | ~ (v7_waybel_0 @ X20)
% 0.78/0.96          | ~ (l1_waybel_0 @ X20 @ X21)
% 0.78/0.96          | ~ (r3_waybel_9 @ X21 @ X20 @ X22)
% 0.78/0.96          | (r2_hidden @ X22 @ (k10_yellow_6 @ X21 @ X20))
% 0.78/0.96          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.78/0.96          | (r3_waybel_9 @ X21 @ X20 @ (sk_D_1 @ X20 @ X21))
% 0.78/0.96          | ~ (l1_pre_topc @ X21)
% 0.78/0.96          | ~ (v1_compts_1 @ X21)
% 0.78/0.96          | ~ (v8_pre_topc @ X21)
% 0.78/0.96          | ~ (v2_pre_topc @ X21)
% 0.78/0.96          | (v2_struct_0 @ X21))),
% 0.78/0.96      inference('cnf', [status(esa)], [t33_waybel_9])).
% 0.78/0.96  thf('485', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | ~ (v2_pre_topc @ sk_A)
% 0.78/0.96          | ~ (v8_pre_topc @ sk_A)
% 0.78/0.96          | ~ (v1_compts_1 @ sk_A)
% 0.78/0.96          | ~ (l1_pre_topc @ sk_A)
% 0.78/0.96          | (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ X0 @ sk_A))
% 0.78/0.96          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.78/0.96          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96          | ~ (v7_waybel_0 @ X0)
% 0.78/0.96          | ~ (v4_orders_2 @ X0)
% 0.78/0.96          | (v2_struct_0 @ X0))),
% 0.78/0.96      inference('sup-', [status(thm)], ['483', '484'])).
% 0.78/0.96  thf('486', plain, ((v2_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('487', plain, ((v8_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('488', plain, ((v1_compts_1 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('489', plain, ((l1_pre_topc @ sk_A)),
% 0.78/0.96      inference('sup-', [status(thm)], ['9', '10'])).
% 0.78/0.96  thf('490', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ X0 @ sk_A))
% 0.78/0.96          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.78/0.96          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96          | ~ (v7_waybel_0 @ X0)
% 0.78/0.96          | ~ (v4_orders_2 @ X0)
% 0.78/0.96          | (v2_struct_0 @ X0))),
% 0.78/0.96      inference('demod', [status(thm)], ['485', '486', '487', '488', '489'])).
% 0.78/0.96  thf('491', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ X0)
% 0.78/0.96          | ~ (v4_orders_2 @ X0)
% 0.78/0.96          | ~ (v7_waybel_0 @ X0)
% 0.78/0.96          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.78/0.96          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.78/0.96          | (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ X0 @ sk_A))
% 0.78/0.96          | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['490'])).
% 0.78/0.96  thf('492', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 0.78/0.96        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.78/0.96        | ~ (v7_waybel_0 @ sk_B)
% 0.78/0.96        | ~ (v4_orders_2 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B))),
% 0.78/0.96      inference('sup-', [status(thm)], ['482', '491'])).
% 0.78/0.96  thf('493', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('494', plain, ((v7_waybel_0 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('495', plain, ((v4_orders_2 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('496', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 0.78/0.96        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96        | (v2_struct_0 @ sk_B))),
% 0.78/0.96      inference('demod', [status(thm)], ['492', '493', '494', '495'])).
% 0.78/0.96  thf('497', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['496'])).
% 0.78/0.96  thf('498', plain,
% 0.78/0.96      (((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_B))),
% 0.78/0.96      inference('sup+', [status(thm)], ['481', '497'])).
% 0.78/0.96  thf('499', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_B)
% 0.78/0.96        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96           (k10_yellow_6 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('simplify', [status(thm)], ['498'])).
% 0.78/0.96  thf('500', plain,
% 0.78/0.96      ((~ (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96           (k10_yellow_6 @ sk_A @ sk_B)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('split', [status(esa)], ['386'])).
% 0.78/0.96  thf('501', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_A)
% 0.78/0.96         | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 0.78/0.96         | (v2_struct_0 @ sk_B)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['499', '500'])).
% 0.78/0.96  thf('502', plain, (~ (v2_struct_0 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('503', plain,
% 0.78/0.96      ((((r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 0.78/0.96         | (v2_struct_0 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('clc', [status(thm)], ['501', '502'])).
% 0.78/0.96  thf('504', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('clc', [status(thm)], ['72', '73'])).
% 0.78/0.96  thf('505', plain,
% 0.78/0.96      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('clc', [status(thm)], ['14', '15'])).
% 0.78/0.96  thf('506', plain,
% 0.78/0.96      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('clc', [status(thm)], ['26', '27'])).
% 0.78/0.96  thf('507', plain,
% 0.78/0.96      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.78/0.96         ((v2_struct_0 @ X20)
% 0.78/0.96          | ~ (v4_orders_2 @ X20)
% 0.78/0.96          | ~ (v7_waybel_0 @ X20)
% 0.78/0.96          | ~ (l1_waybel_0 @ X20 @ X21)
% 0.78/0.96          | ~ (r3_waybel_9 @ X21 @ X20 @ X22)
% 0.78/0.96          | (r2_hidden @ X22 @ (k10_yellow_6 @ X21 @ X20))
% 0.78/0.96          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.78/0.96          | (m1_subset_1 @ (sk_D_1 @ X20 @ X21) @ (u1_struct_0 @ X21))
% 0.78/0.96          | ~ (l1_pre_topc @ X21)
% 0.78/0.96          | ~ (v1_compts_1 @ X21)
% 0.78/0.96          | ~ (v8_pre_topc @ X21)
% 0.78/0.96          | ~ (v2_pre_topc @ X21)
% 0.78/0.96          | (v2_struct_0 @ X21))),
% 0.78/0.96      inference('cnf', [status(esa)], [t33_waybel_9])).
% 0.78/0.96  thf('508', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | ~ (v2_pre_topc @ sk_A)
% 0.78/0.96          | ~ (v8_pre_topc @ sk_A)
% 0.78/0.96          | ~ (v1_compts_1 @ sk_A)
% 0.78/0.96          | ~ (l1_pre_topc @ sk_A)
% 0.78/0.96          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.78/0.96          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96          | ~ (v7_waybel_0 @ X0)
% 0.78/0.96          | ~ (v4_orders_2 @ X0)
% 0.78/0.96          | (v2_struct_0 @ X0))),
% 0.78/0.96      inference('sup-', [status(thm)], ['506', '507'])).
% 0.78/0.96  thf('509', plain, ((v2_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('510', plain, ((v8_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('511', plain, ((v1_compts_1 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('512', plain, ((l1_pre_topc @ sk_A)),
% 0.78/0.96      inference('sup-', [status(thm)], ['9', '10'])).
% 0.78/0.96  thf('513', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.78/0.96          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96          | ~ (v7_waybel_0 @ X0)
% 0.78/0.96          | ~ (v4_orders_2 @ X0)
% 0.78/0.96          | (v2_struct_0 @ X0))),
% 0.78/0.96      inference('demod', [status(thm)], ['508', '509', '510', '511', '512'])).
% 0.78/0.96  thf('514', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ X0)
% 0.78/0.96          | ~ (v4_orders_2 @ X0)
% 0.78/0.96          | ~ (v7_waybel_0 @ X0)
% 0.78/0.96          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.78/0.96          | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 0.78/0.96          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['513'])).
% 0.78/0.96  thf('515', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.78/0.96        | ~ (v7_waybel_0 @ sk_B)
% 0.78/0.96        | ~ (v4_orders_2 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B))),
% 0.78/0.96      inference('sup-', [status(thm)], ['505', '514'])).
% 0.78/0.96  thf('516', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('517', plain, ((v7_waybel_0 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('518', plain, ((v4_orders_2 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('519', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96        | (v2_struct_0 @ sk_B))),
% 0.78/0.96      inference('demod', [status(thm)], ['515', '516', '517', '518'])).
% 0.78/0.96  thf('520', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_hidden @ (sk_C_1 @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['519'])).
% 0.78/0.96  thf('521', plain,
% 0.78/0.96      (((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_B))),
% 0.78/0.96      inference('sup+', [status(thm)], ['504', '520'])).
% 0.78/0.96  thf('522', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_B)
% 0.78/0.96        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96           (k10_yellow_6 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('simplify', [status(thm)], ['521'])).
% 0.78/0.96  thf('523', plain,
% 0.78/0.96      ((~ (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96           (k10_yellow_6 @ sk_A @ sk_B)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('split', [status(esa)], ['386'])).
% 0.78/0.96  thf('524', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_A)
% 0.78/0.96         | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96         | (v2_struct_0 @ sk_B)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['522', '523'])).
% 0.78/0.96  thf('525', plain, (~ (v2_struct_0 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('526', plain,
% 0.78/0.96      ((((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96         | (v2_struct_0 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('clc', [status(thm)], ['524', '525'])).
% 0.78/0.96  thf('527', plain,
% 0.78/0.96      ((((r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 0.78/0.96         | (v2_struct_0 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('clc', [status(thm)], ['501', '502'])).
% 0.78/0.96  thf('528', plain,
% 0.78/0.96      ((((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96         | (v2_struct_0 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('clc', [status(thm)], ['524', '525'])).
% 0.78/0.96  thf('529', plain,
% 0.78/0.96      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.78/0.96         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.78/0.96          | (m1_subset_1 @ (sk_D_2 @ X24) @ (u1_struct_0 @ X24))
% 0.78/0.96          | ~ (v11_waybel_0 @ X25 @ X24)
% 0.78/0.96          | ~ (r3_waybel_9 @ X24 @ X25 @ X23)
% 0.78/0.96          | ((X23) = (k1_waybel_9 @ X24 @ X25))
% 0.78/0.96          | ~ (l1_waybel_0 @ X25 @ X24)
% 0.78/0.96          | ~ (v7_waybel_0 @ X25)
% 0.78/0.96          | ~ (v4_orders_2 @ X25)
% 0.78/0.96          | (v2_struct_0 @ X25)
% 0.78/0.96          | ~ (l1_waybel_9 @ X24)
% 0.78/0.96          | ~ (v1_compts_1 @ X24)
% 0.78/0.96          | ~ (v2_lattice3 @ X24)
% 0.78/0.96          | ~ (v1_lattice3 @ X24)
% 0.78/0.96          | ~ (v5_orders_2 @ X24)
% 0.78/0.96          | ~ (v4_orders_2 @ X24)
% 0.78/0.96          | ~ (v3_orders_2 @ X24)
% 0.78/0.96          | ~ (v8_pre_topc @ X24)
% 0.78/0.96          | ~ (v2_pre_topc @ X24))),
% 0.78/0.96      inference('cnf', [status(esa)], [t36_waybel_9])).
% 0.78/0.96  thf('530', plain,
% 0.78/0.96      ((![X0 : $i]:
% 0.78/0.96          ((v2_struct_0 @ sk_A)
% 0.78/0.96           | ~ (v2_pre_topc @ sk_A)
% 0.78/0.96           | ~ (v8_pre_topc @ sk_A)
% 0.78/0.96           | ~ (v3_orders_2 @ sk_A)
% 0.78/0.96           | ~ (v4_orders_2 @ sk_A)
% 0.78/0.96           | ~ (v5_orders_2 @ sk_A)
% 0.78/0.96           | ~ (v1_lattice3 @ sk_A)
% 0.78/0.96           | ~ (v2_lattice3 @ sk_A)
% 0.78/0.96           | ~ (v1_compts_1 @ sk_A)
% 0.78/0.96           | ~ (l1_waybel_9 @ sk_A)
% 0.78/0.96           | (v2_struct_0 @ X0)
% 0.78/0.96           | ~ (v4_orders_2 @ X0)
% 0.78/0.96           | ~ (v7_waybel_0 @ X0)
% 0.78/0.96           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 0.78/0.96           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_A))
% 0.78/0.96           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['528', '529'])).
% 0.78/0.96  thf('531', plain, ((v2_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('532', plain, ((v8_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('533', plain, ((v3_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('534', plain, ((v4_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('535', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('536', plain, ((v1_lattice3 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('537', plain, ((v2_lattice3 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('538', plain, ((v1_compts_1 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('539', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('540', plain,
% 0.78/0.96      ((![X0 : $i]:
% 0.78/0.96          ((v2_struct_0 @ sk_A)
% 0.78/0.96           | (v2_struct_0 @ X0)
% 0.78/0.96           | ~ (v4_orders_2 @ X0)
% 0.78/0.96           | ~ (v7_waybel_0 @ X0)
% 0.78/0.96           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 0.78/0.96           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_A))
% 0.78/0.96           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('demod', [status(thm)],
% 0.78/0.96                ['530', '531', '532', '533', '534', '535', '536', '537', 
% 0.78/0.96                 '538', '539'])).
% 0.78/0.96  thf('541', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_A)
% 0.78/0.96         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96         | ~ (v11_waybel_0 @ sk_B @ sk_A)
% 0.78/0.96         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.78/0.96         | ~ (v7_waybel_0 @ sk_B)
% 0.78/0.96         | ~ (v4_orders_2 @ sk_B)
% 0.78/0.96         | (v2_struct_0 @ sk_B)
% 0.78/0.96         | (v2_struct_0 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['527', '540'])).
% 0.78/0.96  thf('542', plain, ((v11_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('543', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('544', plain, ((v7_waybel_0 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('545', plain, ((v4_orders_2 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('546', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_A)
% 0.78/0.96         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | (v2_struct_0 @ sk_B)
% 0.78/0.96         | (v2_struct_0 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('demod', [status(thm)], ['541', '542', '543', '544', '545'])).
% 0.78/0.96  thf('547', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_B)
% 0.78/0.96         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.78/0.96         | (v2_struct_0 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('simplify', [status(thm)], ['546'])).
% 0.78/0.96  thf('548', plain,
% 0.78/0.96      (![X26 : $i]:
% 0.78/0.96         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X26) @ sk_A @ sk_A)
% 0.78/0.96          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('549', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_A)
% 0.78/0.96         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | (v2_struct_0 @ sk_B)
% 0.78/0.96         | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_D_2 @ sk_A)) @ sk_A @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['547', '548'])).
% 0.78/0.96  thf('550', plain,
% 0.78/0.96      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.78/0.96         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.78/0.96          | ~ (v5_pre_topc @ (k4_waybel_1 @ X24 @ (sk_D_2 @ X24)) @ X24 @ X24)
% 0.78/0.96          | ~ (v11_waybel_0 @ X25 @ X24)
% 0.78/0.96          | ~ (r3_waybel_9 @ X24 @ X25 @ X23)
% 0.78/0.96          | ((X23) = (k1_waybel_9 @ X24 @ X25))
% 0.78/0.96          | ~ (l1_waybel_0 @ X25 @ X24)
% 0.78/0.96          | ~ (v7_waybel_0 @ X25)
% 0.78/0.96          | ~ (v4_orders_2 @ X25)
% 0.78/0.96          | (v2_struct_0 @ X25)
% 0.78/0.96          | ~ (l1_waybel_9 @ X24)
% 0.78/0.96          | ~ (v1_compts_1 @ X24)
% 0.78/0.96          | ~ (v2_lattice3 @ X24)
% 0.78/0.96          | ~ (v1_lattice3 @ X24)
% 0.78/0.96          | ~ (v5_orders_2 @ X24)
% 0.78/0.96          | ~ (v4_orders_2 @ X24)
% 0.78/0.96          | ~ (v3_orders_2 @ X24)
% 0.78/0.96          | ~ (v8_pre_topc @ X24)
% 0.78/0.96          | ~ (v2_pre_topc @ X24))),
% 0.78/0.96      inference('cnf', [status(esa)], [t36_waybel_9])).
% 0.78/0.96  thf('551', plain,
% 0.78/0.96      ((![X0 : $i, X1 : $i]:
% 0.78/0.96          ((v2_struct_0 @ sk_B)
% 0.78/0.96           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96           | (v2_struct_0 @ sk_A)
% 0.78/0.96           | ~ (v2_pre_topc @ sk_A)
% 0.78/0.96           | ~ (v8_pre_topc @ sk_A)
% 0.78/0.96           | ~ (v3_orders_2 @ sk_A)
% 0.78/0.96           | ~ (v4_orders_2 @ sk_A)
% 0.78/0.96           | ~ (v5_orders_2 @ sk_A)
% 0.78/0.96           | ~ (v1_lattice3 @ sk_A)
% 0.78/0.96           | ~ (v2_lattice3 @ sk_A)
% 0.78/0.96           | ~ (v1_compts_1 @ sk_A)
% 0.78/0.96           | ~ (l1_waybel_9 @ sk_A)
% 0.78/0.96           | (v2_struct_0 @ X0)
% 0.78/0.96           | ~ (v4_orders_2 @ X0)
% 0.78/0.96           | ~ (v7_waybel_0 @ X0)
% 0.78/0.96           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | ((X1) = (k1_waybel_9 @ sk_A @ X0))
% 0.78/0.96           | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 0.78/0.96           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['549', '550'])).
% 0.78/0.96  thf('552', plain, ((v2_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('553', plain, ((v8_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('554', plain, ((v3_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('555', plain, ((v4_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('556', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('557', plain, ((v1_lattice3 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('558', plain, ((v2_lattice3 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('559', plain, ((v1_compts_1 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('560', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('561', plain,
% 0.78/0.96      ((![X0 : $i, X1 : $i]:
% 0.78/0.96          ((v2_struct_0 @ sk_B)
% 0.78/0.96           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96           | (v2_struct_0 @ sk_A)
% 0.78/0.96           | (v2_struct_0 @ X0)
% 0.78/0.96           | ~ (v4_orders_2 @ X0)
% 0.78/0.96           | ~ (v7_waybel_0 @ X0)
% 0.78/0.96           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | ((X1) = (k1_waybel_9 @ sk_A @ X0))
% 0.78/0.96           | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 0.78/0.96           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('demod', [status(thm)],
% 0.78/0.96                ['551', '552', '553', '554', '555', '556', '557', '558', 
% 0.78/0.96                 '559', '560'])).
% 0.78/0.96  thf('562', plain,
% 0.78/0.96      ((![X0 : $i]:
% 0.78/0.96          ((v2_struct_0 @ sk_A)
% 0.78/0.96           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_A))
% 0.78/0.96           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 0.78/0.96           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | ~ (v7_waybel_0 @ X0)
% 0.78/0.96           | ~ (v4_orders_2 @ X0)
% 0.78/0.96           | (v2_struct_0 @ X0)
% 0.78/0.96           | (v2_struct_0 @ sk_A)
% 0.78/0.96           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96           | (v2_struct_0 @ sk_B)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['526', '561'])).
% 0.78/0.96  thf('563', plain,
% 0.78/0.96      ((![X0 : $i]:
% 0.78/0.96          ((v2_struct_0 @ sk_B)
% 0.78/0.96           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96           | (v2_struct_0 @ X0)
% 0.78/0.96           | ~ (v4_orders_2 @ X0)
% 0.78/0.96           | ~ (v7_waybel_0 @ X0)
% 0.78/0.96           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ X0))
% 0.78/0.96           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_A))
% 0.78/0.96           | ~ (v11_waybel_0 @ X0 @ sk_A)
% 0.78/0.96           | (v2_struct_0 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('simplify', [status(thm)], ['562'])).
% 0.78/0.96  thf('564', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_A)
% 0.78/0.96         | (v2_struct_0 @ sk_A)
% 0.78/0.96         | ~ (v11_waybel_0 @ sk_B @ sk_A)
% 0.78/0.96         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.78/0.96         | ~ (v7_waybel_0 @ sk_B)
% 0.78/0.96         | ~ (v4_orders_2 @ sk_B)
% 0.78/0.96         | (v2_struct_0 @ sk_B)
% 0.78/0.96         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | (v2_struct_0 @ sk_B)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['503', '563'])).
% 0.78/0.96  thf('565', plain, ((v11_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('566', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('567', plain, ((v7_waybel_0 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('568', plain, ((v4_orders_2 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('569', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_A)
% 0.78/0.96         | (v2_struct_0 @ sk_A)
% 0.78/0.96         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | (v2_struct_0 @ sk_B)
% 0.78/0.96         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | (v2_struct_0 @ sk_B)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('demod', [status(thm)], ['564', '565', '566', '567', '568'])).
% 0.78/0.96  thf('570', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_B)
% 0.78/0.96         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | (v2_struct_0 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('simplify', [status(thm)], ['569'])).
% 0.78/0.96  thf('571', plain, (~ (v2_struct_0 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('572', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_A)
% 0.78/0.96         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_9 @ sk_A @ sk_B))))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('clc', [status(thm)], ['570', '571'])).
% 0.78/0.96  thf('573', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_9 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('simplify', [status(thm)], ['80'])).
% 0.78/0.96  thf('574', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (m1_subset_1 @ (k1_waybel_9 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('simplify', [status(thm)], ['76'])).
% 0.78/0.96  thf('575', plain,
% 0.78/0.96      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.78/0.96         ((v2_struct_0 @ X20)
% 0.78/0.96          | ~ (v4_orders_2 @ X20)
% 0.78/0.96          | ~ (v7_waybel_0 @ X20)
% 0.78/0.96          | ~ (l1_waybel_0 @ X20 @ X21)
% 0.78/0.96          | ~ (r3_waybel_9 @ X21 @ X20 @ X22)
% 0.78/0.96          | (r2_hidden @ X22 @ (k10_yellow_6 @ X21 @ X20))
% 0.78/0.96          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.78/0.96          | ((sk_C_2 @ X20 @ X21) != (sk_D_1 @ X20 @ X21))
% 0.78/0.96          | ~ (l1_pre_topc @ X21)
% 0.78/0.96          | ~ (v1_compts_1 @ X21)
% 0.78/0.96          | ~ (v8_pre_topc @ X21)
% 0.78/0.96          | ~ (v2_pre_topc @ X21)
% 0.78/0.96          | (v2_struct_0 @ X21))),
% 0.78/0.96      inference('cnf', [status(esa)], [t33_waybel_9])).
% 0.78/0.96  thf('576', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | ~ (v2_pre_topc @ sk_A)
% 0.78/0.96          | ~ (v8_pre_topc @ sk_A)
% 0.78/0.96          | ~ (v1_compts_1 @ sk_A)
% 0.78/0.96          | ~ (l1_pre_topc @ sk_A)
% 0.78/0.96          | ((sk_C_2 @ X0 @ sk_A) != (sk_D_1 @ X0 @ sk_A))
% 0.78/0.96          | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96             (k10_yellow_6 @ sk_A @ X0))
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96          | ~ (v7_waybel_0 @ X0)
% 0.78/0.96          | ~ (v4_orders_2 @ X0)
% 0.78/0.96          | (v2_struct_0 @ X0))),
% 0.78/0.96      inference('sup-', [status(thm)], ['574', '575'])).
% 0.78/0.96  thf('577', plain, ((v2_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('578', plain, ((v8_pre_topc @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('579', plain, ((v1_compts_1 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('580', plain, ((l1_pre_topc @ sk_A)),
% 0.78/0.96      inference('sup-', [status(thm)], ['9', '10'])).
% 0.78/0.96  thf('581', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | ((sk_C_2 @ X0 @ sk_A) != (sk_D_1 @ X0 @ sk_A))
% 0.78/0.96          | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96             (k10_yellow_6 @ sk_A @ X0))
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96          | ~ (v7_waybel_0 @ X0)
% 0.78/0.96          | ~ (v4_orders_2 @ X0)
% 0.78/0.96          | (v2_struct_0 @ X0))),
% 0.78/0.96      inference('demod', [status(thm)], ['576', '577', '578', '579', '580'])).
% 0.78/0.96  thf('582', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ X0)
% 0.78/0.96          | ~ (v4_orders_2 @ X0)
% 0.78/0.96          | ~ (v7_waybel_0 @ X0)
% 0.78/0.96          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.78/0.96          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96          | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96             (k10_yellow_6 @ sk_A @ X0))
% 0.78/0.96          | ((sk_C_2 @ X0 @ sk_A) != (sk_D_1 @ X0 @ sk_A))
% 0.78/0.96          | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['581'])).
% 0.78/0.96  thf('583', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | ((sk_C_2 @ sk_B @ sk_A) != (sk_D_1 @ sk_B @ sk_A))
% 0.78/0.96        | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96           (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.78/0.96        | ~ (v7_waybel_0 @ sk_B)
% 0.78/0.96        | ~ (v4_orders_2 @ sk_B)
% 0.78/0.96        | (v2_struct_0 @ sk_B))),
% 0.78/0.96      inference('sup-', [status(thm)], ['573', '582'])).
% 0.78/0.96  thf('584', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('585', plain, ((v7_waybel_0 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('586', plain, ((v4_orders_2 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('587', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | ((sk_C_2 @ sk_B @ sk_A) != (sk_D_1 @ sk_B @ sk_A))
% 0.78/0.96        | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96           (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96        | (v2_struct_0 @ sk_B))),
% 0.78/0.96      inference('demod', [status(thm)], ['583', '584', '585', '586'])).
% 0.78/0.96  thf('588', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_B)
% 0.78/0.96        | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96           (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96        | ((sk_C_2 @ sk_B @ sk_A) != (sk_D_1 @ sk_B @ sk_A))
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('simplify', [status(thm)], ['587'])).
% 0.78/0.96  thf('589', plain,
% 0.78/0.96      (((((sk_C_2 @ sk_B @ sk_A) != (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | (v2_struct_0 @ sk_A)
% 0.78/0.96         | (v2_struct_0 @ sk_A)
% 0.78/0.96         | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96            (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96         | (v2_struct_0 @ sk_B)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['572', '588'])).
% 0.78/0.96  thf('590', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_B)
% 0.78/0.96         | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96            (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96         | (v2_struct_0 @ sk_A)
% 0.78/0.96         | ((sk_C_2 @ sk_B @ sk_A) != (k1_waybel_9 @ sk_A @ sk_B))))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('simplify', [status(thm)], ['589'])).
% 0.78/0.96  thf('591', plain,
% 0.78/0.96      (((((k1_waybel_9 @ sk_A @ sk_B) != (k1_waybel_9 @ sk_A @ sk_B))
% 0.78/0.96         | (v2_struct_0 @ sk_A)
% 0.78/0.96         | (v2_struct_0 @ sk_A)
% 0.78/0.96         | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96            (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96         | (v2_struct_0 @ sk_B)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['480', '590'])).
% 0.78/0.96  thf('592', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_B)
% 0.78/0.96         | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96            (k10_yellow_6 @ sk_A @ sk_B))
% 0.78/0.96         | (v2_struct_0 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('simplify', [status(thm)], ['591'])).
% 0.78/0.96  thf('593', plain, (~ (v2_struct_0 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('594', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_A)
% 0.78/0.96         | (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96            (k10_yellow_6 @ sk_A @ sk_B))))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('clc', [status(thm)], ['592', '593'])).
% 0.78/0.96  thf('595', plain,
% 0.78/0.96      ((~ (r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96           (k10_yellow_6 @ sk_A @ sk_B)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('split', [status(esa)], ['386'])).
% 0.78/0.96  thf('596', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('clc', [status(thm)], ['594', '595'])).
% 0.78/0.96  thf(cc1_lattice3, axiom,
% 0.78/0.96    (![A:$i]:
% 0.78/0.96     ( ( l1_orders_2 @ A ) =>
% 0.78/0.96       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.78/0.96  thf('597', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         (~ (v1_lattice3 @ X0) | ~ (v2_struct_0 @ X0) | ~ (l1_orders_2 @ X0))),
% 0.78/0.96      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.78/0.96  thf('598', plain,
% 0.78/0.96      (((~ (l1_orders_2 @ sk_A) | ~ (v1_lattice3 @ sk_A)))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['596', '597'])).
% 0.78/0.96  thf('599', plain, ((v1_lattice3 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('600', plain,
% 0.78/0.96      ((~ (l1_orders_2 @ sk_A))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('demod', [status(thm)], ['598', '599'])).
% 0.78/0.96  thf('601', plain,
% 0.78/0.96      ((~ (l1_waybel_9 @ sk_A))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ 
% 0.78/0.96               (k10_yellow_6 @ sk_A @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['388', '600'])).
% 0.78/0.96  thf('602', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('603', plain,
% 0.78/0.96      (((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('demod', [status(thm)], ['601', '602'])).
% 0.78/0.96  thf('604', plain,
% 0.78/0.96      (~ ((r2_waybel_9 @ sk_A @ sk_B)) | 
% 0.78/0.96       ~
% 0.78/0.96       ((r2_hidden @ (k1_waybel_9 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B)))),
% 0.78/0.96      inference('split', [status(esa)], ['386'])).
% 0.78/0.96  thf('605', plain, (~ ((r2_waybel_9 @ sk_A @ sk_B))),
% 0.78/0.96      inference('sat_resolution*', [status(thm)], ['603', '604'])).
% 0.78/0.96  thf('606', plain, (~ (r2_waybel_9 @ sk_A @ sk_B)),
% 0.78/0.96      inference('simpl_trail', [status(thm)], ['387', '605'])).
% 0.78/0.96  thf('607', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 0.78/0.96      inference('clc', [status(thm)], ['385', '606'])).
% 0.78/0.96  thf('608', plain, (~ (v2_struct_0 @ sk_B)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('609', plain, ((v2_struct_0 @ sk_A)),
% 0.78/0.96      inference('clc', [status(thm)], ['607', '608'])).
% 0.78/0.96  thf('610', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         (~ (v1_lattice3 @ X0) | ~ (v2_struct_0 @ X0) | ~ (l1_orders_2 @ X0))),
% 0.78/0.96      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.78/0.96  thf('611', plain, ((~ (l1_orders_2 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['609', '610'])).
% 0.78/0.96  thf('612', plain, ((v1_lattice3 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('613', plain, (~ (l1_orders_2 @ sk_A)),
% 0.78/0.96      inference('demod', [status(thm)], ['611', '612'])).
% 0.78/0.96  thf('614', plain, (~ (l1_waybel_9 @ sk_A)),
% 0.78/0.96      inference('sup-', [status(thm)], ['0', '613'])).
% 0.78/0.96  thf('615', plain, ((l1_waybel_9 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('616', plain, ($false), inference('demod', [status(thm)], ['614', '615'])).
% 0.78/0.96  
% 0.78/0.96  % SZS output end Refutation
% 0.78/0.96  
% 0.78/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
