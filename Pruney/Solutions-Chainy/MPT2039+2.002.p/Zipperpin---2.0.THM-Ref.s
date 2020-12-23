%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jXdveiUmRg

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:36 EST 2020

% Result     : Theorem 26.70s
% Output     : Refutation 26.70s
% Verified   : 
% Statistics : Number of formulae       :  639 (54412 expanded)
%              Number of leaves         :   61 (16418 expanded)
%              Depth                    :  116
%              Number of atoms          : 11288 (1678080 expanded)
%              Number of equality atoms :   94 (4533 expanded)
%              Maximal formula depth    :   29 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_waybel_9_type,type,(
    r1_waybel_9: $i > $i > $o )).

thf(k4_waybel_1_type,type,(
    k4_waybel_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(l1_waybel_9_type,type,(
    l1_waybel_9: $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(k1_waybel_2_type,type,(
    k1_waybel_2: $i > $i > $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v10_waybel_0_type,type,(
    v10_waybel_0: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

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

thf('0',plain,(
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

thf('1',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v7_waybel_0 @ X32 )
      | ~ ( l1_waybel_0 @ X32 @ X33 )
      | ( r3_waybel_9 @ X33 @ X32 @ ( sk_C @ X32 @ X33 ) )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v1_compts_1 @ X33 )
      | ~ ( v8_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t30_waybel_9])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v1_compts_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_waybel_9 @ A )
     => ( ( l1_pre_topc @ A )
        & ( l1_orders_2 @ A ) ) ) )).

thf('7',plain,(
    ! [X22: $i] :
      ( ( l1_pre_topc @ X22 )
      | ~ ( l1_waybel_9 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','3','4','5','8','9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v7_waybel_0 @ X32 )
      | ~ ( l1_waybel_0 @ X32 @ X33 )
      | ( m1_subset_1 @ ( sk_C @ X32 @ X33 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v1_compts_1 @ X33 )
      | ~ ( v8_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t30_waybel_9])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v1_compts_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('21',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17','18','19','20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('27',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

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

thf('28',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X38 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v10_waybel_0 @ X39 @ X38 )
      | ~ ( r3_waybel_9 @ X38 @ X39 @ X37 )
      | ( X37
        = ( k1_waybel_2 @ X38 @ X39 ) )
      | ~ ( l1_waybel_0 @ X39 @ X38 )
      | ~ ( v7_waybel_0 @ X39 )
      | ~ ( v4_orders_2 @ X39 )
      | ( v2_struct_0 @ X39 )
      | ~ ( l1_waybel_9 @ X38 )
      | ~ ( v1_compts_1 @ X38 )
      | ~ ( v2_lattice3 @ X38 )
      | ~ ( v1_lattice3 @ X38 )
      | ~ ( v5_orders_2 @ X38 )
      | ~ ( v4_orders_2 @ X38 )
      | ~ ( v3_orders_2 @ X38 )
      | ~ ( v8_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t35_waybel_9])).

thf('29',plain,(
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
      | ( ( sk_C @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( ( sk_C @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33','34','35','36','37','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v10_waybel_0 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf('41',plain,(
    v10_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X40: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X40 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_D_2 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X38 @ ( sk_D_2 @ X38 ) ) @ X38 @ X38 )
      | ~ ( v10_waybel_0 @ X39 @ X38 )
      | ~ ( r3_waybel_9 @ X38 @ X39 @ X37 )
      | ( X37
        = ( k1_waybel_2 @ X38 @ X39 ) )
      | ~ ( l1_waybel_0 @ X39 @ X38 )
      | ~ ( v7_waybel_0 @ X39 )
      | ~ ( v4_orders_2 @ X39 )
      | ( v2_struct_0 @ X39 )
      | ~ ( l1_waybel_9 @ X38 )
      | ~ ( v1_compts_1 @ X38 )
      | ~ ( v2_lattice3 @ X38 )
      | ~ ( v1_lattice3 @ X38 )
      | ~ ( v5_orders_2 @ X38 )
      | ~ ( v4_orders_2 @ X38 )
      | ~ ( v3_orders_2 @ X38 )
      | ~ ( v8_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t35_waybel_9])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( sk_C @ sk_B @ sk_A )
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
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( sk_C @ sk_B @ sk_A )
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
    inference(demod,[status(thm)],['50','51','52','53','54','55','56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( ( sk_C @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( sk_C @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( ( sk_C @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_waybel_0 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','62'])).

thf('64',plain,(
    v10_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('73',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('76',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('77',plain,
    ( ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('80',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('81',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

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

thf('82',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v7_waybel_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( r2_lattice3 @ X24 @ ( k2_relset_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) @ ( u1_waybel_0 @ X24 @ X23 ) ) @ X25 )
      | ( X26 != X25 )
      | ~ ( r3_waybel_9 @ X24 @ X23 @ X26 )
      | ~ ( v10_waybel_0 @ X23 @ X24 )
      | ( m1_subset_1 @ ( sk_E @ X24 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_waybel_9 @ X24 )
      | ~ ( v1_compts_1 @ X24 )
      | ~ ( v2_lattice3 @ X24 )
      | ~ ( v1_lattice3 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[l48_waybel_9])).

thf('83',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v2_pre_topc @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v1_lattice3 @ X24 )
      | ~ ( v2_lattice3 @ X24 )
      | ~ ( v1_compts_1 @ X24 )
      | ~ ( l1_waybel_9 @ X24 )
      | ( m1_subset_1 @ ( sk_E @ X24 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v10_waybel_0 @ X23 @ X24 )
      | ~ ( r3_waybel_9 @ X24 @ X23 @ X25 )
      | ( r2_lattice3 @ X24 @ ( k2_relset_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) @ ( u1_waybel_0 @ X24 @ X23 ) ) @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ~ ( v7_waybel_0 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
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
    inference('sup-',[status(thm)],['81','83'])).

thf('85',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88','89','90','91','92','93'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v10_waybel_0 @ sk_B @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','94'])).

thf('96',plain,(
    v10_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_C @ sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['79','101'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf(t30_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( v5_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r1_yellow_0 @ A @ C )
                  & ( B
                    = ( k1_yellow_0 @ A @ C ) ) )
               => ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) )
                  & ( r2_lattice3 @ A @ C @ B ) ) )
              & ( ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) )
                  & ( r2_lattice3 @ A @ C @ B ) )
               => ( ( r1_yellow_0 @ A @ C )
                  & ( B
                    = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( zip_tseitin_0 @ D @ C @ B @ A ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('105',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X10 @ X11 )
      | ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k1_yellow_0 @ A @ C ) )
        & ( r1_yellow_0 @ A @ C ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_lattice3 @ A @ C @ D )
       => ( r1_orders_2 @ A @ B @ D ) )
     => ( zip_tseitin_0 @ D @ C @ B @ A ) ) )).

thf(zf_stmt_7,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( ( r2_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( zip_tseitin_1 @ D @ C @ B @ A ) )
               => ( zip_tseitin_2 @ C @ B @ A ) )
              & ( ( ( B
                    = ( k1_yellow_0 @ A @ C ) )
                  & ( r1_yellow_0 @ A @ C ) )
               => ( ( r2_lattice3 @ A @ C @ B )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_lattice3 @ A @ C @ D )
                       => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) )).

thf('107',plain,(
    ! [X15: $i,X16: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( r2_lattice3 @ X16 @ X19 @ X15 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X19 @ X15 @ X16 ) @ X19 @ X15 @ X16 )
      | ( zip_tseitin_2 @ X19 @ X15 @ X16 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v5_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X22: $i] :
      ( ( l1_orders_2 @ X22 )
      | ~ ( l1_waybel_9 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_9])).

thf('112',plain,(
    l1_orders_2 @ sk_A ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['108','109','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','113'])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['104','114'])).

thf('116',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('120',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['115'])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('122',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X10 @ X11 )
      | ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('125',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X7 )
      | ( r2_lattice3 @ X7 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

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

thf('126',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ~ ( v7_waybel_0 @ X27 )
      | ~ ( l1_waybel_0 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r2_lattice3 @ X28 @ ( k2_relset_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) @ ( u1_waybel_0 @ X28 @ X27 ) ) @ X30 )
      | ( r3_orders_2 @ X28 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ( X31 != X29 )
      | ~ ( r3_waybel_9 @ X28 @ X27 @ X31 )
      | ( m1_subset_1 @ ( sk_E_1 @ X28 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_waybel_9 @ X28 )
      | ~ ( v1_compts_1 @ X28 )
      | ~ ( v2_lattice3 @ X28 )
      | ~ ( v1_lattice3 @ X28 )
      | ~ ( v5_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ~ ( v8_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[l49_waybel_9])).

thf('127',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_pre_topc @ X28 )
      | ~ ( v8_pre_topc @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v5_orders_2 @ X28 )
      | ~ ( v1_lattice3 @ X28 )
      | ~ ( v2_lattice3 @ X28 )
      | ~ ( v1_compts_1 @ X28 )
      | ~ ( l1_waybel_9 @ X28 )
      | ( m1_subset_1 @ ( sk_E_1 @ X28 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( r3_waybel_9 @ X28 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ( r3_orders_2 @ X28 @ X29 @ X30 )
      | ~ ( r2_lattice3 @ X28 @ ( k2_relset_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) @ ( u1_waybel_0 @ X28 @ X27 ) ) @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_waybel_0 @ X27 @ X28 )
      | ~ ( v7_waybel_0 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X0 @ ( k2_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X2 ) @ ( u1_waybel_0 @ X2 @ X1 ) ) @ X4 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v7_waybel_0 @ X1 )
      | ~ ( l1_waybel_0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( r3_orders_2 @ X2 @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r3_waybel_9 @ X2 @ X1 @ X3 )
      | ( m1_subset_1 @ ( sk_E_1 @ X2 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_waybel_9 @ X2 )
      | ~ ( v1_compts_1 @ X2 )
      | ~ ( v2_lattice3 @ X2 )
      | ~ ( v1_lattice3 @ X2 )
      | ~ ( v5_orders_2 @ X2 )
      | ~ ( v4_orders_2 @ X2 )
      | ~ ( v3_orders_2 @ X2 )
      | ~ ( v8_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference('sup-',[status(thm)],['125','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
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
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X1 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ X2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','128'])).

thf('130',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X1 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ X2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['129','130','131','132','133','134','135','136','137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ X1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','139'])).

thf('141',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ X1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_0 @ X1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ X1 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['122','145'])).

thf('147',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X10 @ X11 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A )
      | ( zip_tseitin_1 @ X1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ X1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X1 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(eq_fact,[status(thm)],['148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['108','109','112'])).

thf('151',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['121','152'])).

thf('154',plain,
    ( ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( r3_orders_2 @ X1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    l1_orders_2 @ sk_A ),
    inference('sup-',[status(thm)],['110','111'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['154','161'])).

thf('163',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','163'])).

thf('165',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X7 )
      | ~ ( r1_orders_2 @ X7 @ X6 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X10 @ X11 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['108','109','112'])).

thf('171',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','172'])).

thf('174',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_yellow_0 @ X12 @ X13 )
      | ~ ( zip_tseitin_2 @ X13 @ X14 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('176',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf(d3_waybel_9,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( ( r1_waybel_9 @ A @ B )
          <=> ( r1_yellow_0 @ A @ ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) ) ) ) ) ) )).

thf('177',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( r1_yellow_0 @ X21 @ ( k2_relset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) @ ( u1_waybel_0 @ X21 @ X20 ) ) )
      | ( r1_waybel_9 @ X21 @ X20 )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_waybel_9])).

thf('178',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    l1_orders_2 @ sk_A ),
    inference('sup-',[status(thm)],['110','111'])).

thf('180',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,(
    ! [X40: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X40 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['115'])).

thf('185',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('186',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X7 )
      | ( r2_lattice3 @ X7 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('187',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X10 @ X11 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('188',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_lattice3 @ X0 @ X2 @ X3 )
      | ( zip_tseitin_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['108','109','112'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['185','190'])).

thf('192',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ~ ( v7_waybel_0 @ X27 )
      | ~ ( l1_waybel_0 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r2_lattice3 @ X28 @ ( k2_relset_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) @ ( u1_waybel_0 @ X28 @ X27 ) ) @ X30 )
      | ( r3_orders_2 @ X28 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ( X31 != X29 )
      | ~ ( r3_waybel_9 @ X28 @ X27 @ X31 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X28 @ ( sk_E_1 @ X28 ) ) @ X28 @ X28 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_waybel_9 @ X28 )
      | ~ ( v1_compts_1 @ X28 )
      | ~ ( v2_lattice3 @ X28 )
      | ~ ( v1_lattice3 @ X28 )
      | ~ ( v5_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ~ ( v8_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[l49_waybel_9])).

thf('194',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_pre_topc @ X28 )
      | ~ ( v8_pre_topc @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v5_orders_2 @ X28 )
      | ~ ( v1_lattice3 @ X28 )
      | ~ ( v2_lattice3 @ X28 )
      | ~ ( v1_compts_1 @ X28 )
      | ~ ( l1_waybel_9 @ X28 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X28 @ ( sk_E_1 @ X28 ) ) @ X28 @ X28 )
      | ~ ( r3_waybel_9 @ X28 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ( r3_orders_2 @ X28 @ X29 @ X30 )
      | ~ ( r2_lattice3 @ X28 @ ( k2_relset_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) @ ( u1_waybel_0 @ X28 @ X27 ) ) @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_waybel_0 @ X27 @ X28 )
      | ~ ( v7_waybel_0 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
    inference('sup-',[status(thm)],['192','194'])).

thf('196',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['195','196','197','198','199','200','201','202','203','204','205','206','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['184','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['183','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','213'])).

thf('215',plain,
    ( ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','215'])).

thf('217',plain,
    ( ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('219',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','220'])).

thf('222',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X7 )
      | ~ ( r1_orders_2 @ X7 @ X6 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X10 @ X11 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_9 @ sk_A @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['108','109','112'])).

thf('228',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['103','229'])).

thf('231',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['230'])).

thf('232',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_yellow_0 @ X12 @ X13 )
      | ~ ( zip_tseitin_2 @ X13 @ X14 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('233',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( r1_yellow_0 @ X21 @ ( k2_relset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) @ ( u1_waybel_0 @ X21 @ X20 ) ) )
      | ( r1_waybel_9 @ X21 @ X20 )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_waybel_9])).

thf('235',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    l1_orders_2 @ sk_A ),
    inference('sup-',[status(thm)],['110','111'])).

thf('237',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['235','236','237'])).

thf('239',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['238'])).

thf('240',plain,(
    ! [X40: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X40 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v7_waybel_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( r2_lattice3 @ X24 @ ( k2_relset_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) @ ( u1_waybel_0 @ X24 @ X23 ) ) @ X25 )
      | ( X26 != X25 )
      | ~ ( r3_waybel_9 @ X24 @ X23 @ X26 )
      | ~ ( v10_waybel_0 @ X23 @ X24 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X24 @ ( sk_E @ X24 ) ) @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_waybel_9 @ X24 )
      | ~ ( v1_compts_1 @ X24 )
      | ~ ( v2_lattice3 @ X24 )
      | ~ ( v1_lattice3 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[l48_waybel_9])).

thf('243',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v2_pre_topc @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v1_lattice3 @ X24 )
      | ~ ( v2_lattice3 @ X24 )
      | ~ ( v1_compts_1 @ X24 )
      | ~ ( l1_waybel_9 @ X24 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X24 @ ( sk_E @ X24 ) ) @ X24 @ X24 )
      | ~ ( v10_waybel_0 @ X23 @ X24 )
      | ~ ( r3_waybel_9 @ X24 @ X23 @ X25 )
      | ( r2_lattice3 @ X24 @ ( k2_relset_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) @ ( u1_waybel_0 @ X24 @ X23 ) ) @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ~ ( v7_waybel_0 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(simplify,[status(thm)],['242'])).

thf('244',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
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
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ X1 )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ X1 )
      | ~ ( v10_waybel_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['244','245','246','247','248','249','250','251','252','253'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','254'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ X0 ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ~ ( v10_waybel_0 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['255'])).

thf('257',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v10_waybel_0 @ sk_B @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','256'])).

thf('258',plain,(
    v10_waybel_0 @ sk_B @ sk_A ),
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
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['257','258','259','260','261'])).

thf('263',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['262'])).

thf('264',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['262'])).

thf('265',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','113'])).

thf('266',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['264','265'])).

thf('267',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['266'])).

thf('268',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('269',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('270',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['262'])).

thf('271',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['266'])).

thf('272',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['262'])).

thf('273',plain,
    ( ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('274',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,
    ( ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['274'])).

thf('276',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('277',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['277'])).

thf('279',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['271','278'])).

thf('280',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['279'])).

thf('281',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X7 )
      | ~ ( r1_orders_2 @ X7 @ X6 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('282',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['280','281'])).

thf('283',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X10 @ X11 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('284',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['282','283'])).

thf('285',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['108','109','112'])).

thf('286',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['284','285'])).

thf('287',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['286'])).

thf('288',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['270','287'])).

thf('289',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['288'])).

thf('290',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_yellow_0 @ X12 @ X13 )
      | ~ ( zip_tseitin_2 @ X13 @ X14 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('291',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['289','290'])).

thf('292',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( r1_yellow_0 @ X21 @ ( k2_relset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) @ ( u1_waybel_0 @ X21 @ X20 ) ) )
      | ( r1_waybel_9 @ X21 @ X20 )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_waybel_9])).

thf('293',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['291','292'])).

thf('294',plain,(
    l1_orders_2 @ sk_A ),
    inference('sup-',[status(thm)],['110','111'])).

thf('295',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['293','294','295'])).

thf('297',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_E_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['296'])).

thf('298',plain,(
    ! [X40: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X40 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['297','298'])).

thf('300',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['266'])).

thf('301',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['262'])).

thf('302',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('303',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['301','302'])).

thf('304',plain,
    ( ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['303'])).

thf('305',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_pre_topc @ X28 )
      | ~ ( v8_pre_topc @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v5_orders_2 @ X28 )
      | ~ ( v1_lattice3 @ X28 )
      | ~ ( v2_lattice3 @ X28 )
      | ~ ( v1_compts_1 @ X28 )
      | ~ ( l1_waybel_9 @ X28 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X28 @ ( sk_E_1 @ X28 ) ) @ X28 @ X28 )
      | ~ ( r3_waybel_9 @ X28 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ( r3_orders_2 @ X28 @ X29 @ X30 )
      | ~ ( r2_lattice3 @ X28 @ ( k2_relset_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X28 ) @ ( u1_waybel_0 @ X28 @ X27 ) ) @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_waybel_0 @ X27 @ X28 )
      | ~ ( v7_waybel_0 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('306',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
    inference('sup-',[status(thm)],['304','305'])).

thf('307',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('314',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('317',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('319',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['306','307','308','309','310','311','312','313','314','315','316','317','318'])).

thf('320',plain,(
    ! [X0: $i] :
      ( ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['319'])).

thf('321',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['300','320'])).

thf('322',plain,(
    ! [X0: $i] :
      ( ~ ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_E_1 @ sk_A ) ) @ sk_A @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['321'])).

thf('323',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['299','322'])).

thf('324',plain,(
    ! [X0: $i] :
      ( ~ ( r3_waybel_9 @ sk_A @ sk_B @ X0 )
      | ( r3_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['323'])).

thf('325',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['269','324'])).

thf('326',plain,
    ( ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['325'])).

thf('327',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['268','326'])).

thf('328',plain,
    ( ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['327'])).

thf('329',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r3_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('330',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['328','329'])).

thf('331',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['330'])).

thf('332',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['267','331'])).

thf('333',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['332'])).

thf('334',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X7 )
      | ~ ( r1_orders_2 @ X7 @ X6 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('335',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['333','334'])).

thf('336',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X10 @ X11 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('337',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ( r1_waybel_9 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['335','336'])).

thf('338',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( zip_tseitin_1 @ ( sk_D @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['108','109','112'])).

thf('339',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['337','338'])).

thf('340',plain,
    ( ~ ( r2_lattice3 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['339'])).

thf('341',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['263','340'])).

thf('342',plain,
    ( ( zip_tseitin_2 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) @ ( k1_waybel_2 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['341'])).

thf('343',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_yellow_0 @ X12 @ X13 )
      | ~ ( zip_tseitin_2 @ X13 @ X14 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('344',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['342','343'])).

thf('345',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( r1_yellow_0 @ X21 @ ( k2_relset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) @ ( u1_waybel_0 @ X21 @ X20 ) ) )
      | ( r1_waybel_9 @ X21 @ X20 )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_waybel_9])).

thf('346',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['344','345'])).

thf('347',plain,(
    l1_orders_2 @ sk_A ),
    inference('sup-',[status(thm)],['110','111'])).

thf('348',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['346','347','348'])).

thf('350',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['349'])).

thf('351',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('352',plain,
    ( ( r1_waybel_9 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['350','351'])).

thf('353',plain,
    ( ~ ( r1_waybel_9 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('354',plain,
    ( ~ ( r1_waybel_9 @ sk_A @ sk_B )
   <= ~ ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['353'])).

thf('355',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('356',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('357',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

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

thf('358',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v4_orders_2 @ X34 )
      | ~ ( v7_waybel_0 @ X34 )
      | ~ ( l1_waybel_0 @ X34 @ X35 )
      | ~ ( r3_waybel_9 @ X35 @ X34 @ X36 )
      | ( r2_hidden @ X36 @ ( k10_yellow_6 @ X35 @ X34 ) )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ( r3_waybel_9 @ X35 @ X34 @ ( sk_C_1 @ X34 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v1_compts_1 @ X35 )
      | ~ ( v8_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('359',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['357','358'])).

thf('360',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('362',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('363',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('364',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['359','360','361','362','363'])).

thf('365',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['364'])).

thf('366',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['356','365'])).

thf('367',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('368',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('369',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('370',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['366','367','368','369'])).

thf('371',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['370'])).

thf('372',plain,
    ( ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['355','371'])).

thf('373',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['372'])).

thf('374',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['353'])).

thf('375',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['373','374'])).

thf('376',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('377',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['375','376'])).

thf('378',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('379',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('380',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('381',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v4_orders_2 @ X34 )
      | ~ ( v7_waybel_0 @ X34 )
      | ~ ( l1_waybel_0 @ X34 @ X35 )
      | ~ ( r3_waybel_9 @ X35 @ X34 @ X36 )
      | ( r2_hidden @ X36 @ ( k10_yellow_6 @ X35 @ X34 ) )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ( m1_subset_1 @ ( sk_C_1 @ X34 @ X35 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v1_compts_1 @ X35 )
      | ~ ( v8_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('382',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['380','381'])).

thf('383',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('384',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('385',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('386',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('387',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['382','383','384','385','386'])).

thf('388',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['387'])).

thf('389',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['379','388'])).

thf('390',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('391',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('392',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('393',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['389','390','391','392'])).

thf('394',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['393'])).

thf('395',plain,
    ( ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['378','394'])).

thf('396',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['395'])).

thf('397',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['353'])).

thf('398',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['396','397'])).

thf('399',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('400',plain,
    ( ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['398','399'])).

thf('401',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['375','376'])).

thf('402',plain,
    ( ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['398','399'])).

thf('403',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X38 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v10_waybel_0 @ X39 @ X38 )
      | ~ ( r3_waybel_9 @ X38 @ X39 @ X37 )
      | ( X37
        = ( k1_waybel_2 @ X38 @ X39 ) )
      | ~ ( l1_waybel_0 @ X39 @ X38 )
      | ~ ( v7_waybel_0 @ X39 )
      | ~ ( v4_orders_2 @ X39 )
      | ( v2_struct_0 @ X39 )
      | ~ ( l1_waybel_9 @ X38 )
      | ~ ( v1_compts_1 @ X38 )
      | ~ ( v2_lattice3 @ X38 )
      | ~ ( v1_lattice3 @ X38 )
      | ~ ( v5_orders_2 @ X38 )
      | ~ ( v4_orders_2 @ X38 )
      | ~ ( v3_orders_2 @ X38 )
      | ~ ( v8_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t35_waybel_9])).

thf('404',plain,
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
        | ( ( sk_C_1 @ sk_B @ sk_A )
          = ( k1_waybel_2 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
        | ~ ( v10_waybel_0 @ X0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['402','403'])).

thf('405',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('406',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('407',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('408',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('409',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('410',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('411',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('412',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('413',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('414',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( ( sk_C_1 @ sk_B @ sk_A )
          = ( k1_waybel_2 @ sk_A @ X0 ) )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
        | ~ ( v10_waybel_0 @ X0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['404','405','406','407','408','409','410','411','412','413'])).

thf('415',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v10_waybel_0 @ sk_B @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['401','414'])).

thf('416',plain,(
    v10_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('417',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('418',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('419',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('420',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['415','416','417','418','419'])).

thf('421',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['420'])).

thf('422',plain,(
    ! [X40: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X40 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('423',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_D_2 @ sk_A ) ) @ sk_A @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['421','422'])).

thf('424',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X38 @ ( sk_D_2 @ X38 ) ) @ X38 @ X38 )
      | ~ ( v10_waybel_0 @ X39 @ X38 )
      | ~ ( r3_waybel_9 @ X38 @ X39 @ X37 )
      | ( X37
        = ( k1_waybel_2 @ X38 @ X39 ) )
      | ~ ( l1_waybel_0 @ X39 @ X38 )
      | ~ ( v7_waybel_0 @ X39 )
      | ~ ( v4_orders_2 @ X39 )
      | ( v2_struct_0 @ X39 )
      | ~ ( l1_waybel_9 @ X38 )
      | ~ ( v1_compts_1 @ X38 )
      | ~ ( v2_lattice3 @ X38 )
      | ~ ( v1_lattice3 @ X38 )
      | ~ ( v5_orders_2 @ X38 )
      | ~ ( v4_orders_2 @ X38 )
      | ~ ( v3_orders_2 @ X38 )
      | ~ ( v8_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t35_waybel_9])).

thf('425',plain,
    ( ! [X0: $i,X1: $i] :
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
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['423','424'])).

thf('426',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('427',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('428',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('429',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('430',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('431',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('432',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('433',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('434',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('435',plain,
    ( ! [X0: $i,X1: $i] :
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
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['425','426','427','428','429','430','431','432','433','434'])).

thf('436',plain,
    ( ! [X0: $i] :
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
        | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['400','435'])).

thf('437',plain,
    ( ! [X0: $i] :
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
        | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['436'])).

thf('438',plain,
    ( ( ( v2_struct_0 @ sk_A )
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
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['377','437'])).

thf('439',plain,(
    v10_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('440',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('441',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('442',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('443',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['438','439','440','441','442'])).

thf('444',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['443'])).

thf('445',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('446',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['444','445'])).

thf('447',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('448',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('449',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('450',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v4_orders_2 @ X34 )
      | ~ ( v7_waybel_0 @ X34 )
      | ~ ( l1_waybel_0 @ X34 @ X35 )
      | ~ ( r3_waybel_9 @ X35 @ X34 @ X36 )
      | ( r2_hidden @ X36 @ ( k10_yellow_6 @ X35 @ X34 ) )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ( r3_waybel_9 @ X35 @ X34 @ ( sk_D_1 @ X34 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v1_compts_1 @ X35 )
      | ~ ( v8_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('451',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['449','450'])).

thf('452',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('453',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('454',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('455',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('456',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['451','452','453','454','455'])).

thf('457',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D_1 @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['456'])).

thf('458',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['448','457'])).

thf('459',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('460',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('461',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('462',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['458','459','460','461'])).

thf('463',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['462'])).

thf('464',plain,
    ( ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['447','463'])).

thf('465',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['464'])).

thf('466',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['353'])).

thf('467',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['465','466'])).

thf('468',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('469',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['467','468'])).

thf('470',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('471',plain,
    ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('472',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('473',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v4_orders_2 @ X34 )
      | ~ ( v7_waybel_0 @ X34 )
      | ~ ( l1_waybel_0 @ X34 @ X35 )
      | ~ ( r3_waybel_9 @ X35 @ X34 @ X36 )
      | ( r2_hidden @ X36 @ ( k10_yellow_6 @ X35 @ X34 ) )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X34 @ X35 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v1_compts_1 @ X35 )
      | ~ ( v8_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('474',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['472','473'])).

thf('475',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('476',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('477',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('478',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('479',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['474','475','476','477','478'])).

thf('480',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['479'])).

thf('481',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['471','480'])).

thf('482',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('483',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('484',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('485',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['481','482','483','484'])).

thf('486',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['485'])).

thf('487',plain,
    ( ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['470','486'])).

thf('488',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['487'])).

thf('489',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['353'])).

thf('490',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['488','489'])).

thf('491',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('492',plain,
    ( ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['490','491'])).

thf('493',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B @ ( sk_D_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['467','468'])).

thf('494',plain,
    ( ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['490','491'])).

thf('495',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X38 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v10_waybel_0 @ X39 @ X38 )
      | ~ ( r3_waybel_9 @ X38 @ X39 @ X37 )
      | ( X37
        = ( k1_waybel_2 @ X38 @ X39 ) )
      | ~ ( l1_waybel_0 @ X39 @ X38 )
      | ~ ( v7_waybel_0 @ X39 )
      | ~ ( v4_orders_2 @ X39 )
      | ( v2_struct_0 @ X39 )
      | ~ ( l1_waybel_9 @ X38 )
      | ~ ( v1_compts_1 @ X38 )
      | ~ ( v2_lattice3 @ X38 )
      | ~ ( v1_lattice3 @ X38 )
      | ~ ( v5_orders_2 @ X38 )
      | ~ ( v4_orders_2 @ X38 )
      | ~ ( v3_orders_2 @ X38 )
      | ~ ( v8_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t35_waybel_9])).

thf('496',plain,
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
    inference('sup-',[status(thm)],['494','495'])).

thf('497',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('498',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('499',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('500',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('501',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('502',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('503',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('504',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('505',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('506',plain,
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
    inference(demod,[status(thm)],['496','497','498','499','500','501','502','503','504','505'])).

thf('507',plain,
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
    inference('sup-',[status(thm)],['493','506'])).

thf('508',plain,(
    v10_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('509',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('510',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('511',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('512',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['507','508','509','510','511'])).

thf('513',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['512'])).

thf('514',plain,(
    ! [X40: $i] :
      ( ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ X40 ) @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('515',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( k4_waybel_1 @ sk_A @ ( sk_D_2 @ sk_A ) ) @ sk_A @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['513','514'])).

thf('516',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ~ ( v5_pre_topc @ ( k4_waybel_1 @ X38 @ ( sk_D_2 @ X38 ) ) @ X38 @ X38 )
      | ~ ( v10_waybel_0 @ X39 @ X38 )
      | ~ ( r3_waybel_9 @ X38 @ X39 @ X37 )
      | ( X37
        = ( k1_waybel_2 @ X38 @ X39 ) )
      | ~ ( l1_waybel_0 @ X39 @ X38 )
      | ~ ( v7_waybel_0 @ X39 )
      | ~ ( v4_orders_2 @ X39 )
      | ( v2_struct_0 @ X39 )
      | ~ ( l1_waybel_9 @ X38 )
      | ~ ( v1_compts_1 @ X38 )
      | ~ ( v2_lattice3 @ X38 )
      | ~ ( v1_lattice3 @ X38 )
      | ~ ( v5_orders_2 @ X38 )
      | ~ ( v4_orders_2 @ X38 )
      | ~ ( v3_orders_2 @ X38 )
      | ~ ( v8_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t35_waybel_9])).

thf('517',plain,
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
    inference('sup-',[status(thm)],['515','516'])).

thf('518',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('519',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('520',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('521',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('522',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('523',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('524',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('525',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('526',plain,(
    l1_waybel_9 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('527',plain,
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
    inference(demod,[status(thm)],['517','518','519','520','521','522','523','524','525','526'])).

thf('528',plain,
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
    inference('sup-',[status(thm)],['492','527'])).

thf('529',plain,
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
    inference(simplify,[status(thm)],['528'])).

thf('530',plain,
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
    inference('sup-',[status(thm)],['469','529'])).

thf('531',plain,(
    v10_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('532',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('533',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('534',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('535',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['530','531','532','533','534'])).

thf('536',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['535'])).

thf('537',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('538',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_1 @ sk_B @ sk_A )
        = ( k1_waybel_2 @ sk_A @ sk_B ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['536','537'])).

thf('539',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ sk_B @ ( k1_waybel_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('540',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('541',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v4_orders_2 @ X34 )
      | ~ ( v7_waybel_0 @ X34 )
      | ~ ( l1_waybel_0 @ X34 @ X35 )
      | ~ ( r3_waybel_9 @ X35 @ X34 @ X36 )
      | ( r2_hidden @ X36 @ ( k10_yellow_6 @ X35 @ X34 ) )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ( ( sk_C_1 @ X34 @ X35 )
       != ( sk_D_1 @ X34 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v1_compts_1 @ X35 )
      | ~ ( v8_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t33_waybel_9])).

thf('542',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v8_pre_topc @ sk_A )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( ( sk_C_1 @ X0 @ sk_A )
       != ( sk_D_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['540','541'])).

thf('543',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('544',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('545',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('546',plain,(
    l1_pre_topc @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('547',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C_1 @ X0 @ sk_A )
       != ( sk_D_1 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['542','543','544','545','546'])).

thf('548',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ X0 ) )
      | ( ( sk_C_1 @ X0 @ sk_A )
       != ( sk_D_1 @ X0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['547'])).

thf('549',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
     != ( sk_D_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['539','548'])).

thf('550',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('551',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('552',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('553',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_C_1 @ sk_B @ sk_A )
     != ( sk_D_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['549','550','551','552'])).

thf('554',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( ( sk_C_1 @ sk_B @ sk_A )
     != ( sk_D_1 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['553'])).

thf('555',plain,
    ( ( ( ( sk_C_1 @ sk_B @ sk_A )
       != ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['538','554'])).

thf('556',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_A )
       != ( k1_waybel_2 @ sk_A @ sk_B ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['555'])).

thf('557',plain,
    ( ( ( ( k1_waybel_2 @ sk_A @ sk_B )
       != ( k1_waybel_2 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['446','556'])).

thf('558',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['557'])).

thf('559',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('560',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['558','559'])).

thf('561',plain,
    ( ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['353'])).

thf('562',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['560','561'])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('563',plain,(
    ! [X3: $i] :
      ( ~ ( v1_lattice3 @ X3 )
      | ~ ( v2_struct_0 @ X3 )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('564',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_lattice3 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['562','563'])).

thf('565',plain,(
    l1_orders_2 @ sk_A ),
    inference('sup-',[status(thm)],['110','111'])).

thf('566',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('567',plain,(
    r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['564','565','566'])).

thf('568',plain,
    ( ~ ( r1_waybel_9 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ ( k1_waybel_2 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['353'])).

thf('569',plain,(
    ~ ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['567','568'])).

thf('570',plain,(
    ~ ( r1_waybel_9 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['354','569'])).

thf('571',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['352','570'])).

thf('572',plain,(
    ! [X3: $i] :
      ( ~ ( v1_lattice3 @ X3 )
      | ~ ( v2_struct_0 @ X3 )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('573',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['571','572'])).

thf('574',plain,(
    l1_orders_2 @ sk_A ),
    inference('sup-',[status(thm)],['110','111'])).

thf('575',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('576',plain,(
    $false ),
    inference(demod,[status(thm)],['573','574','575'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jXdveiUmRg
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:16:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 26.70/26.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 26.70/26.89  % Solved by: fo/fo7.sh
% 26.70/26.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 26.70/26.89  % done 6026 iterations in 26.402s
% 26.70/26.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 26.70/26.89  % SZS output start Refutation
% 26.70/26.89  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 26.70/26.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 26.70/26.89  thf(r1_waybel_9_type, type, r1_waybel_9: $i > $i > $o).
% 26.70/26.89  thf(k4_waybel_1_type, type, k4_waybel_1: $i > $i > $i).
% 26.70/26.89  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 26.70/26.89  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 26.70/26.89  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 26.70/26.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 26.70/26.89  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 26.70/26.89  thf(l1_waybel_9_type, type, l1_waybel_9: $i > $o).
% 26.70/26.89  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 26.70/26.89  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 26.70/26.89  thf(k1_waybel_2_type, type, k1_waybel_2: $i > $i > $i).
% 26.70/26.89  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 26.70/26.89  thf(sk_A_type, type, sk_A: $i).
% 26.70/26.89  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 26.70/26.89  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 26.70/26.89  thf(sk_E_type, type, sk_E: $i > $i).
% 26.70/26.89  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 26.70/26.89  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 26.70/26.89  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 26.70/26.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 26.70/26.89  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 26.70/26.89  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 26.70/26.89  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 26.70/26.89  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 26.70/26.89  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 26.70/26.89  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 26.70/26.89  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 26.70/26.89  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 26.70/26.89  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 26.70/26.89  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 26.70/26.89  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 26.70/26.89  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 26.70/26.89  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 26.70/26.89  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 26.70/26.89  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 26.70/26.89  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 26.70/26.89  thf(v10_waybel_0_type, type, v10_waybel_0: $i > $i > $o).
% 26.70/26.89  thf(sk_D_2_type, type, sk_D_2: $i > $i).
% 26.70/26.89  thf(sk_B_type, type, sk_B: $i).
% 26.70/26.89  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 26.70/26.89  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 26.70/26.89  thf(t38_waybel_9, conjecture,
% 26.70/26.89    (![A:$i]:
% 26.70/26.89     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 26.70/26.89         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 26.70/26.89         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 26.70/26.89       ( ( ![B:$i]:
% 26.70/26.89           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.89             ( v5_pre_topc @ ( k4_waybel_1 @ A @ B ) @ A @ A ) ) ) =>
% 26.70/26.89         ( ![B:$i]:
% 26.70/26.89           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 26.70/26.89               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 26.70/26.89             ( ( v10_waybel_0 @ B @ A ) =>
% 26.70/26.89               ( ( r1_waybel_9 @ A @ B ) & 
% 26.70/26.89                 ( r2_hidden @
% 26.70/26.89                   ( k1_waybel_2 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ))).
% 26.70/26.89  thf(zf_stmt_0, negated_conjecture,
% 26.70/26.89    (~( ![A:$i]:
% 26.70/26.89        ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 26.70/26.89            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 26.70/26.89            ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 26.70/26.89          ( ( ![B:$i]:
% 26.70/26.89              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.89                ( v5_pre_topc @ ( k4_waybel_1 @ A @ B ) @ A @ A ) ) ) =>
% 26.70/26.89            ( ![B:$i]:
% 26.70/26.89              ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 26.70/26.89                  ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 26.70/26.89                ( ( v10_waybel_0 @ B @ A ) =>
% 26.70/26.89                  ( ( r1_waybel_9 @ A @ B ) & 
% 26.70/26.89                    ( r2_hidden @
% 26.70/26.89                      ( k1_waybel_2 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ) )),
% 26.70/26.89    inference('cnf.neg', [status(esa)], [t38_waybel_9])).
% 26.70/26.89  thf('0', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf(t30_waybel_9, axiom,
% 26.70/26.89    (![A:$i]:
% 26.70/26.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 26.70/26.89         ( v8_pre_topc @ A ) & ( v1_compts_1 @ A ) & ( l1_pre_topc @ A ) ) =>
% 26.70/26.89       ( ![B:$i]:
% 26.70/26.89         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 26.70/26.89             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 26.70/26.89           ( ?[C:$i]:
% 26.70/26.89             ( ( r3_waybel_9 @ A @ B @ C ) & 
% 26.70/26.89               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 26.70/26.89  thf('1', plain,
% 26.70/26.89      (![X32 : $i, X33 : $i]:
% 26.70/26.89         ((v2_struct_0 @ X32)
% 26.70/26.89          | ~ (v4_orders_2 @ X32)
% 26.70/26.89          | ~ (v7_waybel_0 @ X32)
% 26.70/26.89          | ~ (l1_waybel_0 @ X32 @ X33)
% 26.70/26.89          | (r3_waybel_9 @ X33 @ X32 @ (sk_C @ X32 @ X33))
% 26.70/26.89          | ~ (l1_pre_topc @ X33)
% 26.70/26.89          | ~ (v1_compts_1 @ X33)
% 26.70/26.89          | ~ (v8_pre_topc @ X33)
% 26.70/26.89          | ~ (v2_pre_topc @ X33)
% 26.70/26.89          | (v2_struct_0 @ X33))),
% 26.70/26.89      inference('cnf', [status(esa)], [t30_waybel_9])).
% 26.70/26.89  thf('2', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | ~ (v2_pre_topc @ sk_A)
% 26.70/26.89        | ~ (v8_pre_topc @ sk_A)
% 26.70/26.89        | ~ (v1_compts_1 @ sk_A)
% 26.70/26.89        | ~ (l1_pre_topc @ sk_A)
% 26.70/26.89        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 26.70/26.89        | ~ (v7_waybel_0 @ sk_B)
% 26.70/26.89        | ~ (v4_orders_2 @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_B))),
% 26.70/26.89      inference('sup-', [status(thm)], ['0', '1'])).
% 26.70/26.89  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('4', plain, ((v8_pre_topc @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('5', plain, ((v1_compts_1 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('6', plain, ((l1_waybel_9 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf(dt_l1_waybel_9, axiom,
% 26.70/26.89    (![A:$i]:
% 26.70/26.89     ( ( l1_waybel_9 @ A ) => ( ( l1_pre_topc @ A ) & ( l1_orders_2 @ A ) ) ))).
% 26.70/26.89  thf('7', plain, (![X22 : $i]: ((l1_pre_topc @ X22) | ~ (l1_waybel_9 @ X22))),
% 26.70/26.89      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 26.70/26.89  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 26.70/26.89      inference('sup-', [status(thm)], ['6', '7'])).
% 26.70/26.89  thf('9', plain, ((v7_waybel_0 @ sk_B)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('10', plain, ((v4_orders_2 @ sk_B)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('11', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B))),
% 26.70/26.89      inference('demod', [status(thm)], ['2', '3', '4', '5', '8', '9', '10'])).
% 26.70/26.89  thf('12', plain, (~ (v2_struct_0 @ sk_B)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('13', plain,
% 26.70/26.89      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('clc', [status(thm)], ['11', '12'])).
% 26.70/26.89  thf('14', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('15', plain,
% 26.70/26.89      (![X32 : $i, X33 : $i]:
% 26.70/26.89         ((v2_struct_0 @ X32)
% 26.70/26.89          | ~ (v4_orders_2 @ X32)
% 26.70/26.89          | ~ (v7_waybel_0 @ X32)
% 26.70/26.89          | ~ (l1_waybel_0 @ X32 @ X33)
% 26.70/26.89          | (m1_subset_1 @ (sk_C @ X32 @ X33) @ (u1_struct_0 @ X33))
% 26.70/26.89          | ~ (l1_pre_topc @ X33)
% 26.70/26.89          | ~ (v1_compts_1 @ X33)
% 26.70/26.89          | ~ (v8_pre_topc @ X33)
% 26.70/26.89          | ~ (v2_pre_topc @ X33)
% 26.70/26.89          | (v2_struct_0 @ X33))),
% 26.70/26.89      inference('cnf', [status(esa)], [t30_waybel_9])).
% 26.70/26.89  thf('16', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | ~ (v2_pre_topc @ sk_A)
% 26.70/26.89        | ~ (v8_pre_topc @ sk_A)
% 26.70/26.89        | ~ (v1_compts_1 @ sk_A)
% 26.70/26.89        | ~ (l1_pre_topc @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | ~ (v7_waybel_0 @ sk_B)
% 26.70/26.89        | ~ (v4_orders_2 @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_B))),
% 26.70/26.89      inference('sup-', [status(thm)], ['14', '15'])).
% 26.70/26.89  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('18', plain, ((v8_pre_topc @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('19', plain, ((v1_compts_1 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 26.70/26.89      inference('sup-', [status(thm)], ['6', '7'])).
% 26.70/26.89  thf('21', plain, ((v7_waybel_0 @ sk_B)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('22', plain, ((v4_orders_2 @ sk_B)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('23', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B))),
% 26.70/26.89      inference('demod', [status(thm)],
% 26.70/26.89                ['16', '17', '18', '19', '20', '21', '22'])).
% 26.70/26.89  thf('24', plain, (~ (v2_struct_0 @ sk_B)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('25', plain,
% 26.70/26.89      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('clc', [status(thm)], ['23', '24'])).
% 26.70/26.89  thf('26', plain,
% 26.70/26.89      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('clc', [status(thm)], ['11', '12'])).
% 26.70/26.89  thf('27', plain,
% 26.70/26.89      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('clc', [status(thm)], ['23', '24'])).
% 26.70/26.89  thf(t35_waybel_9, axiom,
% 26.70/26.89    (![A:$i]:
% 26.70/26.89     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 26.70/26.89         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 26.70/26.89         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 26.70/26.89       ( ![B:$i]:
% 26.70/26.89         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.89           ( ![C:$i]:
% 26.70/26.89             ( ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 26.70/26.89                 ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) =>
% 26.70/26.89               ( ( ( ![D:$i]:
% 26.70/26.89                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.89                       ( v5_pre_topc @ ( k4_waybel_1 @ A @ D ) @ A @ A ) ) ) & 
% 26.70/26.89                   ( v10_waybel_0 @ C @ A ) & ( r3_waybel_9 @ A @ C @ B ) ) =>
% 26.70/26.89                 ( ( B ) = ( k1_waybel_2 @ A @ C ) ) ) ) ) ) ) ))).
% 26.70/26.89  thf('28', plain,
% 26.70/26.89      (![X37 : $i, X38 : $i, X39 : $i]:
% 26.70/26.89         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 26.70/26.89          | (m1_subset_1 @ (sk_D_2 @ X38) @ (u1_struct_0 @ X38))
% 26.70/26.89          | ~ (v10_waybel_0 @ X39 @ X38)
% 26.70/26.89          | ~ (r3_waybel_9 @ X38 @ X39 @ X37)
% 26.70/26.89          | ((X37) = (k1_waybel_2 @ X38 @ X39))
% 26.70/26.89          | ~ (l1_waybel_0 @ X39 @ X38)
% 26.70/26.89          | ~ (v7_waybel_0 @ X39)
% 26.70/26.89          | ~ (v4_orders_2 @ X39)
% 26.70/26.89          | (v2_struct_0 @ X39)
% 26.70/26.89          | ~ (l1_waybel_9 @ X38)
% 26.70/26.89          | ~ (v1_compts_1 @ X38)
% 26.70/26.89          | ~ (v2_lattice3 @ X38)
% 26.70/26.89          | ~ (v1_lattice3 @ X38)
% 26.70/26.89          | ~ (v5_orders_2 @ X38)
% 26.70/26.89          | ~ (v4_orders_2 @ X38)
% 26.70/26.89          | ~ (v3_orders_2 @ X38)
% 26.70/26.89          | ~ (v8_pre_topc @ X38)
% 26.70/26.89          | ~ (v2_pre_topc @ X38))),
% 26.70/26.89      inference('cnf', [status(esa)], [t35_waybel_9])).
% 26.70/26.89  thf('29', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | ~ (v2_pre_topc @ sk_A)
% 26.70/26.89          | ~ (v8_pre_topc @ sk_A)
% 26.70/26.89          | ~ (v3_orders_2 @ sk_A)
% 26.70/26.89          | ~ (v4_orders_2 @ sk_A)
% 26.70/26.89          | ~ (v5_orders_2 @ sk_A)
% 26.70/26.89          | ~ (v1_lattice3 @ sk_A)
% 26.70/26.89          | ~ (v2_lattice3 @ sk_A)
% 26.70/26.89          | ~ (v1_compts_1 @ sk_A)
% 26.70/26.89          | ~ (l1_waybel_9 @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ X0)
% 26.70/26.89          | ~ (v4_orders_2 @ X0)
% 26.70/26.89          | ~ (v7_waybel_0 @ X0)
% 26.70/26.89          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 26.70/26.89          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('sup-', [status(thm)], ['27', '28'])).
% 26.70/26.89  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('31', plain, ((v8_pre_topc @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('32', plain, ((v3_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('33', plain, ((v4_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('34', plain, ((v5_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('35', plain, ((v1_lattice3 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('36', plain, ((v2_lattice3 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('37', plain, ((v1_compts_1 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('38', plain, ((l1_waybel_9 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('39', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ X0)
% 26.70/26.89          | ~ (v4_orders_2 @ X0)
% 26.70/26.89          | ~ (v7_waybel_0 @ X0)
% 26.70/26.89          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 26.70/26.89          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('demod', [status(thm)],
% 26.70/26.89                ['29', '30', '31', '32', '33', '34', '35', '36', '37', '38'])).
% 26.70/26.89  thf('40', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | ~ (v10_waybel_0 @ sk_B @ sk_A)
% 26.70/26.89        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 26.70/26.89        | ~ (v7_waybel_0 @ sk_B)
% 26.70/26.89        | ~ (v4_orders_2 @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['26', '39'])).
% 26.70/26.89  thf('41', plain, ((v10_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('42', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('43', plain, ((v7_waybel_0 @ sk_B)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('44', plain, ((v4_orders_2 @ sk_B)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('45', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 26.70/26.89  thf('46', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_B)
% 26.70/26.89        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89        | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['45'])).
% 26.70/26.89  thf('47', plain,
% 26.70/26.89      (![X40 : $i]:
% 26.70/26.89         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X40) @ sk_A @ sk_A)
% 26.70/26.89          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('48', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_D_2 @ sk_A)) @ sk_A @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['46', '47'])).
% 26.70/26.89  thf('49', plain,
% 26.70/26.89      (![X37 : $i, X38 : $i, X39 : $i]:
% 26.70/26.89         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 26.70/26.89          | ~ (v5_pre_topc @ (k4_waybel_1 @ X38 @ (sk_D_2 @ X38)) @ X38 @ X38)
% 26.70/26.89          | ~ (v10_waybel_0 @ X39 @ X38)
% 26.70/26.89          | ~ (r3_waybel_9 @ X38 @ X39 @ X37)
% 26.70/26.89          | ((X37) = (k1_waybel_2 @ X38 @ X39))
% 26.70/26.89          | ~ (l1_waybel_0 @ X39 @ X38)
% 26.70/26.89          | ~ (v7_waybel_0 @ X39)
% 26.70/26.89          | ~ (v4_orders_2 @ X39)
% 26.70/26.89          | (v2_struct_0 @ X39)
% 26.70/26.89          | ~ (l1_waybel_9 @ X38)
% 26.70/26.89          | ~ (v1_compts_1 @ X38)
% 26.70/26.89          | ~ (v2_lattice3 @ X38)
% 26.70/26.89          | ~ (v1_lattice3 @ X38)
% 26.70/26.89          | ~ (v5_orders_2 @ X38)
% 26.70/26.89          | ~ (v4_orders_2 @ X38)
% 26.70/26.89          | ~ (v3_orders_2 @ X38)
% 26.70/26.89          | ~ (v8_pre_topc @ X38)
% 26.70/26.89          | ~ (v2_pre_topc @ X38))),
% 26.70/26.89      inference('cnf', [status(esa)], [t35_waybel_9])).
% 26.70/26.89  thf('50', plain,
% 26.70/26.89      (![X0 : $i, X1 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_B)
% 26.70/26.89          | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89          | (v2_struct_0 @ sk_A)
% 26.70/26.89          | ~ (v2_pre_topc @ sk_A)
% 26.70/26.89          | ~ (v8_pre_topc @ sk_A)
% 26.70/26.89          | ~ (v3_orders_2 @ sk_A)
% 26.70/26.89          | ~ (v4_orders_2 @ sk_A)
% 26.70/26.89          | ~ (v5_orders_2 @ sk_A)
% 26.70/26.89          | ~ (v1_lattice3 @ sk_A)
% 26.70/26.89          | ~ (v2_lattice3 @ sk_A)
% 26.70/26.89          | ~ (v1_compts_1 @ sk_A)
% 26.70/26.89          | ~ (l1_waybel_9 @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ X0)
% 26.70/26.89          | ~ (v4_orders_2 @ X0)
% 26.70/26.89          | ~ (v7_waybel_0 @ X0)
% 26.70/26.89          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | ((X1) = (k1_waybel_2 @ sk_A @ X0))
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 26.70/26.89          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('sup-', [status(thm)], ['48', '49'])).
% 26.70/26.89  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('52', plain, ((v8_pre_topc @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('53', plain, ((v3_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('54', plain, ((v4_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('55', plain, ((v5_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('56', plain, ((v1_lattice3 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('57', plain, ((v2_lattice3 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('58', plain, ((v1_compts_1 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('59', plain, ((l1_waybel_9 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('60', plain,
% 26.70/26.89      (![X0 : $i, X1 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_B)
% 26.70/26.89          | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89          | (v2_struct_0 @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ X0)
% 26.70/26.89          | ~ (v4_orders_2 @ X0)
% 26.70/26.89          | ~ (v7_waybel_0 @ X0)
% 26.70/26.89          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | ((X1) = (k1_waybel_2 @ sk_A @ X0))
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 26.70/26.89          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('demod', [status(thm)],
% 26.70/26.89                ['50', '51', '52', '53', '54', '55', '56', '57', '58', '59'])).
% 26.70/26.89  thf('61', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 26.70/26.89          | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 26.70/26.89          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | ~ (v7_waybel_0 @ X0)
% 26.70/26.89          | ~ (v4_orders_2 @ X0)
% 26.70/26.89          | (v2_struct_0 @ X0)
% 26.70/26.89          | (v2_struct_0 @ sk_A)
% 26.70/26.89          | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89          | (v2_struct_0 @ sk_B))),
% 26.70/26.89      inference('sup-', [status(thm)], ['25', '60'])).
% 26.70/26.89  thf('62', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_B)
% 26.70/26.89          | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89          | (v2_struct_0 @ X0)
% 26.70/26.89          | ~ (v4_orders_2 @ X0)
% 26.70/26.89          | ~ (v7_waybel_0 @ X0)
% 26.70/26.89          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 26.70/26.89          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['61'])).
% 26.70/26.89  thf('63', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | ~ (v10_waybel_0 @ sk_B @ sk_A)
% 26.70/26.89        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 26.70/26.89        | ~ (v7_waybel_0 @ sk_B)
% 26.70/26.89        | ~ (v4_orders_2 @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89        | (v2_struct_0 @ sk_B))),
% 26.70/26.89      inference('sup-', [status(thm)], ['13', '62'])).
% 26.70/26.89  thf('64', plain, ((v10_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('65', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('66', plain, ((v7_waybel_0 @ sk_B)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('67', plain, ((v4_orders_2 @ sk_B)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('68', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89        | (v2_struct_0 @ sk_B))),
% 26.70/26.89      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 26.70/26.89  thf('69', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_B)
% 26.70/26.89        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['68'])).
% 26.70/26.89  thf('70', plain, (~ (v2_struct_0 @ sk_B)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('71', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.89      inference('clc', [status(thm)], ['69', '70'])).
% 26.70/26.89  thf('72', plain,
% 26.70/26.89      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('clc', [status(thm)], ['11', '12'])).
% 26.70/26.89  thf('73', plain,
% 26.70/26.89      (((r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('sup+', [status(thm)], ['71', '72'])).
% 26.70/26.89  thf('74', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.89      inference('simplify', [status(thm)], ['73'])).
% 26.70/26.89  thf('75', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.89      inference('clc', [status(thm)], ['69', '70'])).
% 26.70/26.89  thf('76', plain,
% 26.70/26.89      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('clc', [status(thm)], ['23', '24'])).
% 26.70/26.89  thf('77', plain,
% 26.70/26.89      (((m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('sup+', [status(thm)], ['75', '76'])).
% 26.70/26.89  thf('78', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('simplify', [status(thm)], ['77'])).
% 26.70/26.89  thf('79', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.89      inference('clc', [status(thm)], ['69', '70'])).
% 26.70/26.89  thf('80', plain,
% 26.70/26.89      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('clc', [status(thm)], ['11', '12'])).
% 26.70/26.89  thf('81', plain,
% 26.70/26.89      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('clc', [status(thm)], ['23', '24'])).
% 26.70/26.89  thf(l48_waybel_9, axiom,
% 26.70/26.89    (![A:$i]:
% 26.70/26.89     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 26.70/26.89         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 26.70/26.89         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 26.70/26.89       ( ![B:$i]:
% 26.70/26.89         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 26.70/26.89             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 26.70/26.89           ( ![C:$i]:
% 26.70/26.89             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.89               ( ![D:$i]:
% 26.70/26.89                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.89                   ( ( ( ( C ) = ( D ) ) & 
% 26.70/26.89                       ( ![E:$i]:
% 26.70/26.89                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.89                           ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) ) ) & 
% 26.70/26.89                       ( v10_waybel_0 @ B @ A ) & ( r3_waybel_9 @ A @ B @ C ) ) =>
% 26.70/26.89                     ( r2_lattice3 @
% 26.70/26.89                       A @ 
% 26.70/26.89                       ( k2_relset_1 @
% 26.70/26.89                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 26.70/26.89                         ( u1_waybel_0 @ A @ B ) ) @ 
% 26.70/26.89                       D ) ) ) ) ) ) ) ) ))).
% 26.70/26.89  thf('82', plain,
% 26.70/26.89      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 26.70/26.89         ((v2_struct_0 @ X23)
% 26.70/26.89          | ~ (v4_orders_2 @ X23)
% 26.70/26.89          | ~ (v7_waybel_0 @ X23)
% 26.70/26.89          | ~ (l1_waybel_0 @ X23 @ X24)
% 26.70/26.89          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 26.70/26.89          | (r2_lattice3 @ X24 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24) @ 
% 26.70/26.89              (u1_waybel_0 @ X24 @ X23)) @ 
% 26.70/26.89             X25)
% 26.70/26.89          | ((X26) != (X25))
% 26.70/26.89          | ~ (r3_waybel_9 @ X24 @ X23 @ X26)
% 26.70/26.89          | ~ (v10_waybel_0 @ X23 @ X24)
% 26.70/26.89          | (m1_subset_1 @ (sk_E @ X24) @ (u1_struct_0 @ X24))
% 26.70/26.89          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 26.70/26.89          | ~ (l1_waybel_9 @ X24)
% 26.70/26.89          | ~ (v1_compts_1 @ X24)
% 26.70/26.89          | ~ (v2_lattice3 @ X24)
% 26.70/26.89          | ~ (v1_lattice3 @ X24)
% 26.70/26.89          | ~ (v5_orders_2 @ X24)
% 26.70/26.89          | ~ (v4_orders_2 @ X24)
% 26.70/26.89          | ~ (v3_orders_2 @ X24)
% 26.70/26.89          | ~ (v8_pre_topc @ X24)
% 26.70/26.89          | ~ (v2_pre_topc @ X24))),
% 26.70/26.89      inference('cnf', [status(esa)], [l48_waybel_9])).
% 26.70/26.89  thf('83', plain,
% 26.70/26.89      (![X23 : $i, X24 : $i, X25 : $i]:
% 26.70/26.89         (~ (v2_pre_topc @ X24)
% 26.70/26.89          | ~ (v8_pre_topc @ X24)
% 26.70/26.89          | ~ (v3_orders_2 @ X24)
% 26.70/26.89          | ~ (v4_orders_2 @ X24)
% 26.70/26.89          | ~ (v5_orders_2 @ X24)
% 26.70/26.89          | ~ (v1_lattice3 @ X24)
% 26.70/26.89          | ~ (v2_lattice3 @ X24)
% 26.70/26.89          | ~ (v1_compts_1 @ X24)
% 26.70/26.89          | ~ (l1_waybel_9 @ X24)
% 26.70/26.89          | (m1_subset_1 @ (sk_E @ X24) @ (u1_struct_0 @ X24))
% 26.70/26.89          | ~ (v10_waybel_0 @ X23 @ X24)
% 26.70/26.89          | ~ (r3_waybel_9 @ X24 @ X23 @ X25)
% 26.70/26.89          | (r2_lattice3 @ X24 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24) @ 
% 26.70/26.89              (u1_waybel_0 @ X24 @ X23)) @ 
% 26.70/26.89             X25)
% 26.70/26.89          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 26.70/26.89          | ~ (l1_waybel_0 @ X23 @ X24)
% 26.70/26.89          | ~ (v7_waybel_0 @ X23)
% 26.70/26.89          | ~ (v4_orders_2 @ X23)
% 26.70/26.89          | (v2_struct_0 @ X23))),
% 26.70/26.89      inference('simplify', [status(thm)], ['82'])).
% 26.70/26.89  thf('84', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ X0)
% 26.70/26.89          | ~ (v4_orders_2 @ X0)
% 26.70/26.89          | ~ (v7_waybel_0 @ X0)
% 26.70/26.89          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | (r2_lattice3 @ sk_A @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ X0)) @ 
% 26.70/26.89             (sk_C @ sk_B @ sk_A))
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 26.70/26.89          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | ~ (l1_waybel_9 @ sk_A)
% 26.70/26.89          | ~ (v1_compts_1 @ sk_A)
% 26.70/26.89          | ~ (v2_lattice3 @ sk_A)
% 26.70/26.89          | ~ (v1_lattice3 @ sk_A)
% 26.70/26.89          | ~ (v5_orders_2 @ sk_A)
% 26.70/26.89          | ~ (v4_orders_2 @ sk_A)
% 26.70/26.89          | ~ (v3_orders_2 @ sk_A)
% 26.70/26.89          | ~ (v8_pre_topc @ sk_A)
% 26.70/26.89          | ~ (v2_pre_topc @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['81', '83'])).
% 26.70/26.89  thf('85', plain, ((l1_waybel_9 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('86', plain, ((v1_compts_1 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('87', plain, ((v2_lattice3 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('88', plain, ((v1_lattice3 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('89', plain, ((v5_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('90', plain, ((v4_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('91', plain, ((v3_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('92', plain, ((v8_pre_topc @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('93', plain, ((v2_pre_topc @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('94', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ X0)
% 26.70/26.89          | ~ (v4_orders_2 @ X0)
% 26.70/26.89          | ~ (v7_waybel_0 @ X0)
% 26.70/26.89          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | (r2_lattice3 @ sk_A @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ X0)) @ 
% 26.70/26.89             (sk_C @ sk_B @ sk_A))
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 26.70/26.89          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('demod', [status(thm)],
% 26.70/26.89                ['84', '85', '86', '87', '88', '89', '90', '91', '92', '93'])).
% 26.70/26.89  thf('95', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | ~ (v10_waybel_0 @ sk_B @ sk_A)
% 26.70/26.89        | (r2_lattice3 @ sk_A @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (sk_C @ sk_B @ sk_A))
% 26.70/26.89        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 26.70/26.89        | ~ (v7_waybel_0 @ sk_B)
% 26.70/26.89        | ~ (v4_orders_2 @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['80', '94'])).
% 26.70/26.89  thf('96', plain, ((v10_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('97', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('98', plain, ((v7_waybel_0 @ sk_B)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('99', plain, ((v4_orders_2 @ sk_B)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('100', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (r2_lattice3 @ sk_A @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (sk_C @ sk_B @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('demod', [status(thm)], ['95', '96', '97', '98', '99'])).
% 26.70/26.89  thf('101', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_B)
% 26.70/26.89        | (r2_lattice3 @ sk_A @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (sk_C @ sk_B @ sk_A))
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['100'])).
% 26.70/26.89  thf('102', plain,
% 26.70/26.89      (((r2_lattice3 @ sk_A @ 
% 26.70/26.89         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89         (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B))),
% 26.70/26.89      inference('sup+', [status(thm)], ['79', '101'])).
% 26.70/26.89  thf('103', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (r2_lattice3 @ sk_A @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.89      inference('simplify', [status(thm)], ['102'])).
% 26.70/26.89  thf('104', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (r2_lattice3 @ sk_A @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.89      inference('simplify', [status(thm)], ['102'])).
% 26.70/26.89  thf(t30_yellow_0, axiom,
% 26.70/26.89    (![A:$i]:
% 26.70/26.89     ( ( ( l1_orders_2 @ A ) & ( v5_orders_2 @ A ) ) =>
% 26.70/26.89       ( ![B:$i]:
% 26.70/26.89         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.89           ( ![C:$i]:
% 26.70/26.89             ( ( ( ( r1_yellow_0 @ A @ C ) & 
% 26.70/26.89                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) =>
% 26.70/26.89                 ( ( ![D:$i]:
% 26.70/26.89                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.89                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 26.70/26.89                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 26.70/26.89                   ( r2_lattice3 @ A @ C @ B ) ) ) & 
% 26.70/26.89               ( ( ( ![D:$i]:
% 26.70/26.89                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.89                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 26.70/26.89                         ( r1_orders_2 @ A @ B @ D ) ) ) ) & 
% 26.70/26.89                   ( r2_lattice3 @ A @ C @ B ) ) =>
% 26.70/26.89                 ( ( r1_yellow_0 @ A @ C ) & 
% 26.70/26.89                   ( ( B ) = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ))).
% 26.70/26.89  thf(zf_stmt_1, axiom,
% 26.70/26.89    (![D:$i,C:$i,B:$i,A:$i]:
% 26.70/26.89     ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.89         ( zip_tseitin_0 @ D @ C @ B @ A ) ) =>
% 26.70/26.89       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 26.70/26.89  thf('105', plain,
% 26.70/26.89      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 26.70/26.89         ((zip_tseitin_1 @ X8 @ X9 @ X10 @ X11)
% 26.70/26.89          | (m1_subset_1 @ X8 @ (u1_struct_0 @ X11)))),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_1])).
% 26.70/26.89  thf('106', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('simplify', [status(thm)], ['77'])).
% 26.70/26.89  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 26.70/26.89  thf(zf_stmt_3, axiom,
% 26.70/26.89    (![C:$i,B:$i,A:$i]:
% 26.70/26.89     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 26.70/26.89       ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & ( r1_yellow_0 @ A @ C ) ) ))).
% 26.70/26.89  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 26.70/26.89  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 26.70/26.89  thf(zf_stmt_6, axiom,
% 26.70/26.89    (![D:$i,C:$i,B:$i,A:$i]:
% 26.70/26.89     ( ( ( r2_lattice3 @ A @ C @ D ) => ( r1_orders_2 @ A @ B @ D ) ) =>
% 26.70/26.89       ( zip_tseitin_0 @ D @ C @ B @ A ) ))).
% 26.70/26.89  thf(zf_stmt_7, axiom,
% 26.70/26.89    (![A:$i]:
% 26.70/26.89     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 26.70/26.89       ( ![B:$i]:
% 26.70/26.89         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.89           ( ![C:$i]:
% 26.70/26.89             ( ( ( ( r2_lattice3 @ A @ C @ B ) & 
% 26.70/26.89                   ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 26.70/26.89                 ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 26.70/26.89               ( ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & 
% 26.70/26.89                   ( r1_yellow_0 @ A @ C ) ) =>
% 26.70/26.89                 ( ( r2_lattice3 @ A @ C @ B ) & 
% 26.70/26.89                   ( ![D:$i]:
% 26.70/26.89                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.89                       ( ( r2_lattice3 @ A @ C @ D ) =>
% 26.70/26.89                         ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 26.70/26.89  thf('107', plain,
% 26.70/26.89      (![X15 : $i, X16 : $i, X19 : $i]:
% 26.70/26.89         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 26.70/26.89          | ~ (r2_lattice3 @ X16 @ X19 @ X15)
% 26.70/26.89          | ~ (zip_tseitin_1 @ (sk_D @ X19 @ X15 @ X16) @ X19 @ X15 @ X16)
% 26.70/26.89          | (zip_tseitin_2 @ X19 @ X15 @ X16)
% 26.70/26.89          | ~ (l1_orders_2 @ X16)
% 26.70/26.89          | ~ (v5_orders_2 @ X16))),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_7])).
% 26.70/26.89  thf('108', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | ~ (v5_orders_2 @ sk_A)
% 26.70/26.89          | ~ (l1_orders_2 @ sk_A)
% 26.70/26.89          | (zip_tseitin_2 @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | ~ (zip_tseitin_1 @ 
% 26.70/26.89               (sk_D @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ X0 @ 
% 26.70/26.89               (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.89      inference('sup-', [status(thm)], ['106', '107'])).
% 26.70/26.89  thf('109', plain, ((v5_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('110', plain, ((l1_waybel_9 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('111', plain,
% 26.70/26.89      (![X22 : $i]: ((l1_orders_2 @ X22) | ~ (l1_waybel_9 @ X22))),
% 26.70/26.89      inference('cnf', [status(esa)], [dt_l1_waybel_9])).
% 26.70/26.89  thf('112', plain, ((l1_orders_2 @ sk_A)),
% 26.70/26.89      inference('sup-', [status(thm)], ['110', '111'])).
% 26.70/26.89  thf('113', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | (zip_tseitin_2 @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | ~ (zip_tseitin_1 @ 
% 26.70/26.89               (sk_D @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ X0 @ 
% 26.70/26.89               (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.89      inference('demod', [status(thm)], ['108', '109', '112'])).
% 26.70/26.89  thf('114', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((m1_subset_1 @ (sk_D @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.89           (u1_struct_0 @ sk_A))
% 26.70/26.89          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89          | (zip_tseitin_2 @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['105', '113'])).
% 26.70/26.89  thf('115', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ 
% 26.70/26.89           (sk_D @ 
% 26.70/26.89            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.89           (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('sup-', [status(thm)], ['104', '114'])).
% 26.70/26.89  thf('116', plain,
% 26.70/26.89      (((m1_subset_1 @ 
% 26.70/26.89         (sk_D @ 
% 26.70/26.89          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89          (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.89         (u1_struct_0 @ sk_A))
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['115'])).
% 26.70/26.89  thf('117', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('simplify', [status(thm)], ['77'])).
% 26.70/26.89  thf('118', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.89      inference('simplify', [status(thm)], ['73'])).
% 26.70/26.89  thf('119', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (r2_lattice3 @ sk_A @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.89      inference('simplify', [status(thm)], ['102'])).
% 26.70/26.89  thf('120', plain,
% 26.70/26.89      (((m1_subset_1 @ 
% 26.70/26.89         (sk_D @ 
% 26.70/26.89          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89          (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.89         (u1_struct_0 @ sk_A))
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['115'])).
% 26.70/26.89  thf('121', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (r2_lattice3 @ sk_A @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.89      inference('simplify', [status(thm)], ['102'])).
% 26.70/26.89  thf('122', plain,
% 26.70/26.89      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 26.70/26.89         ((zip_tseitin_1 @ X8 @ X9 @ X10 @ X11)
% 26.70/26.89          | (m1_subset_1 @ X8 @ (u1_struct_0 @ X11)))),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_1])).
% 26.70/26.89  thf('123', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.89      inference('simplify', [status(thm)], ['73'])).
% 26.70/26.89  thf('124', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('simplify', [status(thm)], ['77'])).
% 26.70/26.89  thf('125', plain,
% 26.70/26.89      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 26.70/26.89         ((zip_tseitin_0 @ X4 @ X5 @ X6 @ X7) | (r2_lattice3 @ X7 @ X5 @ X4))),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_6])).
% 26.70/26.89  thf(l49_waybel_9, axiom,
% 26.70/26.89    (![A:$i]:
% 26.70/26.89     ( ( ( v2_pre_topc @ A ) & ( v8_pre_topc @ A ) & ( v3_orders_2 @ A ) & 
% 26.70/26.89         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & 
% 26.70/26.89         ( v2_lattice3 @ A ) & ( v1_compts_1 @ A ) & ( l1_waybel_9 @ A ) ) =>
% 26.70/26.89       ( ![B:$i]:
% 26.70/26.89         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 26.70/26.89             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 26.70/26.89           ( ![C:$i]:
% 26.70/26.89             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.89               ( ![D:$i]:
% 26.70/26.89                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.89                   ( ( ( ( C ) = ( D ) ) & 
% 26.70/26.89                       ( ![E:$i]:
% 26.70/26.89                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.89                           ( v5_pre_topc @ ( k4_waybel_1 @ A @ E ) @ A @ A ) ) ) & 
% 26.70/26.89                       ( r3_waybel_9 @ A @ B @ C ) ) =>
% 26.70/26.89                     ( ![E:$i]:
% 26.70/26.89                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.89                         ( ( r2_lattice3 @
% 26.70/26.89                             A @ 
% 26.70/26.89                             ( k2_relset_1 @
% 26.70/26.89                               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 26.70/26.89                               ( u1_waybel_0 @ A @ B ) ) @ 
% 26.70/26.89                             E ) =>
% 26.70/26.89                           ( r3_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 26.70/26.89  thf('126', plain,
% 26.70/26.89      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 26.70/26.89         ((v2_struct_0 @ X27)
% 26.70/26.89          | ~ (v4_orders_2 @ X27)
% 26.70/26.89          | ~ (v7_waybel_0 @ X27)
% 26.70/26.89          | ~ (l1_waybel_0 @ X27 @ X28)
% 26.70/26.89          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 26.70/26.89          | ~ (r2_lattice3 @ X28 @ 
% 26.70/26.89               (k2_relset_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28) @ 
% 26.70/26.89                (u1_waybel_0 @ X28 @ X27)) @ 
% 26.70/26.89               X30)
% 26.70/26.89          | (r3_orders_2 @ X28 @ X29 @ X30)
% 26.70/26.89          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 26.70/26.89          | ((X31) != (X29))
% 26.70/26.89          | ~ (r3_waybel_9 @ X28 @ X27 @ X31)
% 26.70/26.89          | (m1_subset_1 @ (sk_E_1 @ X28) @ (u1_struct_0 @ X28))
% 26.70/26.89          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X28))
% 26.70/26.89          | ~ (l1_waybel_9 @ X28)
% 26.70/26.89          | ~ (v1_compts_1 @ X28)
% 26.70/26.89          | ~ (v2_lattice3 @ X28)
% 26.70/26.89          | ~ (v1_lattice3 @ X28)
% 26.70/26.89          | ~ (v5_orders_2 @ X28)
% 26.70/26.89          | ~ (v4_orders_2 @ X28)
% 26.70/26.89          | ~ (v3_orders_2 @ X28)
% 26.70/26.89          | ~ (v8_pre_topc @ X28)
% 26.70/26.89          | ~ (v2_pre_topc @ X28))),
% 26.70/26.89      inference('cnf', [status(esa)], [l49_waybel_9])).
% 26.70/26.89  thf('127', plain,
% 26.70/26.89      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 26.70/26.89         (~ (v2_pre_topc @ X28)
% 26.70/26.89          | ~ (v8_pre_topc @ X28)
% 26.70/26.89          | ~ (v3_orders_2 @ X28)
% 26.70/26.89          | ~ (v4_orders_2 @ X28)
% 26.70/26.89          | ~ (v5_orders_2 @ X28)
% 26.70/26.89          | ~ (v1_lattice3 @ X28)
% 26.70/26.89          | ~ (v2_lattice3 @ X28)
% 26.70/26.89          | ~ (v1_compts_1 @ X28)
% 26.70/26.89          | ~ (l1_waybel_9 @ X28)
% 26.70/26.89          | (m1_subset_1 @ (sk_E_1 @ X28) @ (u1_struct_0 @ X28))
% 26.70/26.89          | ~ (r3_waybel_9 @ X28 @ X27 @ X29)
% 26.70/26.89          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 26.70/26.89          | (r3_orders_2 @ X28 @ X29 @ X30)
% 26.70/26.89          | ~ (r2_lattice3 @ X28 @ 
% 26.70/26.89               (k2_relset_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28) @ 
% 26.70/26.89                (u1_waybel_0 @ X28 @ X27)) @ 
% 26.70/26.89               X30)
% 26.70/26.89          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 26.70/26.89          | ~ (l1_waybel_0 @ X27 @ X28)
% 26.70/26.89          | ~ (v7_waybel_0 @ X27)
% 26.70/26.89          | ~ (v4_orders_2 @ X27)
% 26.70/26.89          | (v2_struct_0 @ X27))),
% 26.70/26.89      inference('simplify', [status(thm)], ['126'])).
% 26.70/26.89  thf('128', plain,
% 26.70/26.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 26.70/26.89         ((zip_tseitin_0 @ X0 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2) @ 
% 26.70/26.89            (u1_waybel_0 @ X2 @ X1)) @ 
% 26.70/26.89           X4 @ X2)
% 26.70/26.89          | (v2_struct_0 @ X1)
% 26.70/26.89          | ~ (v4_orders_2 @ X1)
% 26.70/26.89          | ~ (v7_waybel_0 @ X1)
% 26.70/26.89          | ~ (l1_waybel_0 @ X1 @ X2)
% 26.70/26.89          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 26.70/26.89          | (r3_orders_2 @ X2 @ X3 @ X0)
% 26.70/26.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X2))
% 26.70/26.89          | ~ (r3_waybel_9 @ X2 @ X1 @ X3)
% 26.70/26.89          | (m1_subset_1 @ (sk_E_1 @ X2) @ (u1_struct_0 @ X2))
% 26.70/26.89          | ~ (l1_waybel_9 @ X2)
% 26.70/26.89          | ~ (v1_compts_1 @ X2)
% 26.70/26.89          | ~ (v2_lattice3 @ X2)
% 26.70/26.89          | ~ (v1_lattice3 @ X2)
% 26.70/26.89          | ~ (v5_orders_2 @ X2)
% 26.70/26.89          | ~ (v4_orders_2 @ X2)
% 26.70/26.89          | ~ (v3_orders_2 @ X2)
% 26.70/26.89          | ~ (v8_pre_topc @ X2)
% 26.70/26.89          | ~ (v2_pre_topc @ X2))),
% 26.70/26.89      inference('sup-', [status(thm)], ['125', '127'])).
% 26.70/26.89  thf('129', plain,
% 26.70/26.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | ~ (v2_pre_topc @ sk_A)
% 26.70/26.89          | ~ (v8_pre_topc @ sk_A)
% 26.70/26.89          | ~ (v3_orders_2 @ sk_A)
% 26.70/26.89          | ~ (v4_orders_2 @ sk_A)
% 26.70/26.89          | ~ (v5_orders_2 @ sk_A)
% 26.70/26.89          | ~ (v1_lattice3 @ sk_A)
% 26.70/26.89          | ~ (v2_lattice3 @ sk_A)
% 26.70/26.89          | ~ (v1_compts_1 @ sk_A)
% 26.70/26.89          | ~ (l1_waybel_9 @ sk_A)
% 26.70/26.89          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X1)
% 26.70/26.89          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | ~ (v7_waybel_0 @ X0)
% 26.70/26.89          | ~ (v4_orders_2 @ X0)
% 26.70/26.89          | (v2_struct_0 @ X0)
% 26.70/26.89          | (zip_tseitin_0 @ X1 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ X0)) @ 
% 26.70/26.89             X2 @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['124', '128'])).
% 26.70/26.89  thf('130', plain, ((v2_pre_topc @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('131', plain, ((v8_pre_topc @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('132', plain, ((v3_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('133', plain, ((v4_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('134', plain, ((v5_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('135', plain, ((v1_lattice3 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('136', plain, ((v2_lattice3 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('137', plain, ((v1_compts_1 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('138', plain, ((l1_waybel_9 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('139', plain,
% 26.70/26.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X1)
% 26.70/26.89          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | ~ (v7_waybel_0 @ X0)
% 26.70/26.89          | ~ (v4_orders_2 @ X0)
% 26.70/26.89          | (v2_struct_0 @ X0)
% 26.70/26.89          | (zip_tseitin_0 @ X1 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ X0)) @ 
% 26.70/26.89             X2 @ sk_A))),
% 26.70/26.89      inference('demod', [status(thm)],
% 26.70/26.89                ['129', '130', '131', '132', '133', '134', '135', '136', 
% 26.70/26.89                 '137', '138'])).
% 26.70/26.89  thf('140', plain,
% 26.70/26.89      (![X0 : $i, X1 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | (zip_tseitin_0 @ X1 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             X0 @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | ~ (v4_orders_2 @ sk_B)
% 26.70/26.89          | ~ (v7_waybel_0 @ sk_B)
% 26.70/26.89          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 26.70/26.89          | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X1)
% 26.70/26.89          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['123', '139'])).
% 26.70/26.89  thf('141', plain, ((v4_orders_2 @ sk_B)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('142', plain, ((v7_waybel_0 @ sk_B)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('143', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('144', plain,
% 26.70/26.89      (![X0 : $i, X1 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | (zip_tseitin_0 @ X1 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             X0 @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X1)
% 26.70/26.89          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 26.70/26.89  thf('145', plain,
% 26.70/26.89      (![X0 : $i, X1 : $i]:
% 26.70/26.89         ((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X1)
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | (zip_tseitin_0 @ X1 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             X0 @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['144'])).
% 26.70/26.89  thf('146', plain,
% 26.70/26.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 26.70/26.89         ((zip_tseitin_1 @ X0 @ X3 @ X2 @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ sk_A)
% 26.70/26.89          | (zip_tseitin_0 @ X0 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             X1 @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 26.70/26.89          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('sup-', [status(thm)], ['122', '145'])).
% 26.70/26.89  thf('147', plain,
% 26.70/26.89      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 26.70/26.89         ((zip_tseitin_1 @ X8 @ X9 @ X10 @ X11)
% 26.70/26.89          | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X11))),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_1])).
% 26.70/26.89  thf('148', plain,
% 26.70/26.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 26.70/26.89         ((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X1)
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | (v2_struct_0 @ sk_A)
% 26.70/26.89          | (zip_tseitin_1 @ X1 @ X3 @ X2 @ sk_A)
% 26.70/26.89          | (zip_tseitin_1 @ X1 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             X0 @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['146', '147'])).
% 26.70/26.89  thf('149', plain,
% 26.70/26.89      (![X0 : $i, X1 : $i]:
% 26.70/26.89         ((zip_tseitin_1 @ X1 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           X0 @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X1)
% 26.70/26.89          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('eq_fact', [status(thm)], ['148'])).
% 26.70/26.89  thf('150', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | (zip_tseitin_2 @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | ~ (zip_tseitin_1 @ 
% 26.70/26.89               (sk_D @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ X0 @ 
% 26.70/26.89               (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.89      inference('demod', [status(thm)], ['108', '109', '112'])).
% 26.70/26.89  thf('151', plain,
% 26.70/26.89      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.89           (sk_D @ 
% 26.70/26.89            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | ~ (r2_lattice3 @ sk_A @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['149', '150'])).
% 26.70/26.89  thf('152', plain,
% 26.70/26.89      (((zip_tseitin_2 @ 
% 26.70/26.89         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89         (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | ~ (r2_lattice3 @ sk_A @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.89           (sk_D @ 
% 26.70/26.89            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('simplify', [status(thm)], ['151'])).
% 26.70/26.89  thf('153', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.89           (sk_D @ 
% 26.70/26.89            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['121', '152'])).
% 26.70/26.89  thf('154', plain,
% 26.70/26.89      (((zip_tseitin_2 @ 
% 26.70/26.89         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89         (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.89           (sk_D @ 
% 26.70/26.89            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['153'])).
% 26.70/26.89  thf('155', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('simplify', [status(thm)], ['77'])).
% 26.70/26.89  thf(redefinition_r3_orders_2, axiom,
% 26.70/26.89    (![A:$i,B:$i,C:$i]:
% 26.70/26.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 26.70/26.89         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 26.70/26.89         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 26.70/26.89       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 26.70/26.89  thf('156', plain,
% 26.70/26.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.70/26.89         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 26.70/26.89          | ~ (l1_orders_2 @ X1)
% 26.70/26.89          | ~ (v3_orders_2 @ X1)
% 26.70/26.89          | (v2_struct_0 @ X1)
% 26.70/26.89          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 26.70/26.89          | (r1_orders_2 @ X1 @ X0 @ X2)
% 26.70/26.89          | ~ (r3_orders_2 @ X1 @ X0 @ X2))),
% 26.70/26.89      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 26.70/26.89  thf('157', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | ~ (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 26.70/26.89          | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 26.70/26.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (v2_struct_0 @ sk_A)
% 26.70/26.89          | ~ (v3_orders_2 @ sk_A)
% 26.70/26.89          | ~ (l1_orders_2 @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['155', '156'])).
% 26.70/26.89  thf('158', plain, ((v3_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('159', plain, ((l1_orders_2 @ sk_A)),
% 26.70/26.89      inference('sup-', [status(thm)], ['110', '111'])).
% 26.70/26.89  thf('160', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | ~ (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 26.70/26.89          | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 26.70/26.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('demod', [status(thm)], ['157', '158', '159'])).
% 26.70/26.89  thf('161', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 26.70/26.89          | ~ (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 26.70/26.89          | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['160'])).
% 26.70/26.89  thf('162', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.89           (sk_D @ 
% 26.70/26.89            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89        | ~ (m1_subset_1 @ 
% 26.70/26.89             (sk_D @ 
% 26.70/26.89              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.89             (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('sup-', [status(thm)], ['154', '161'])).
% 26.70/26.89  thf('163', plain,
% 26.70/26.89      ((~ (m1_subset_1 @ 
% 26.70/26.89           (sk_D @ 
% 26.70/26.89            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.89           (u1_struct_0 @ sk_A))
% 26.70/26.89        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.89           (sk_D @ 
% 26.70/26.89            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['162'])).
% 26.70/26.89  thf('164', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.89           (sk_D @ 
% 26.70/26.89            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)))),
% 26.70/26.89      inference('sup-', [status(thm)], ['120', '163'])).
% 26.70/26.89  thf('165', plain,
% 26.70/26.89      (((r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.89         (sk_D @ 
% 26.70/26.89          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89          (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['164'])).
% 26.70/26.89  thf('166', plain,
% 26.70/26.89      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 26.70/26.89         ((zip_tseitin_0 @ X4 @ X5 @ X6 @ X7) | ~ (r1_orders_2 @ X7 @ X6 @ X4))),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_6])).
% 26.70/26.89  thf('167', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | (zip_tseitin_2 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (zip_tseitin_0 @ 
% 26.70/26.89             (sk_D @ 
% 26.70/26.89              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.89             X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['165', '166'])).
% 26.70/26.89  thf('168', plain,
% 26.70/26.89      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 26.70/26.89         ((zip_tseitin_1 @ X8 @ X9 @ X10 @ X11)
% 26.70/26.89          | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X11))),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_1])).
% 26.70/26.89  thf('169', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (zip_tseitin_2 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (v2_struct_0 @ sk_A)
% 26.70/26.89          | (zip_tseitin_1 @ 
% 26.70/26.89             (sk_D @ 
% 26.70/26.89              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.89             X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['167', '168'])).
% 26.70/26.89  thf('170', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | (zip_tseitin_2 @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | ~ (zip_tseitin_1 @ 
% 26.70/26.89               (sk_D @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ X0 @ 
% 26.70/26.89               (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.89      inference('demod', [status(thm)], ['108', '109', '112'])).
% 26.70/26.89  thf('171', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | ~ (r2_lattice3 @ sk_A @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['169', '170'])).
% 26.70/26.89  thf('172', plain,
% 26.70/26.89      ((~ (r2_lattice3 @ sk_A @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['171'])).
% 26.70/26.89  thf('173', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('sup-', [status(thm)], ['119', '172'])).
% 26.70/26.89  thf('174', plain,
% 26.70/26.89      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['173'])).
% 26.70/26.89  thf('175', plain,
% 26.70/26.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 26.70/26.89         ((r1_yellow_0 @ X12 @ X13) | ~ (zip_tseitin_2 @ X13 @ X14 @ X12))),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_3])).
% 26.70/26.89  thf('176', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (r1_yellow_0 @ sk_A @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B))))),
% 26.70/26.89      inference('sup-', [status(thm)], ['174', '175'])).
% 26.70/26.89  thf(d3_waybel_9, axiom,
% 26.70/26.89    (![A:$i]:
% 26.70/26.89     ( ( l1_orders_2 @ A ) =>
% 26.70/26.89       ( ![B:$i]:
% 26.70/26.89         ( ( l1_waybel_0 @ B @ A ) =>
% 26.70/26.89           ( ( r1_waybel_9 @ A @ B ) <=>
% 26.70/26.89             ( r1_yellow_0 @
% 26.70/26.89               A @ 
% 26.70/26.89               ( k2_relset_1 @
% 26.70/26.89                 ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 26.70/26.89                 ( u1_waybel_0 @ A @ B ) ) ) ) ) ) ))).
% 26.70/26.89  thf('177', plain,
% 26.70/26.89      (![X20 : $i, X21 : $i]:
% 26.70/26.89         (~ (l1_waybel_0 @ X20 @ X21)
% 26.70/26.89          | ~ (r1_yellow_0 @ X21 @ 
% 26.70/26.89               (k2_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21) @ 
% 26.70/26.89                (u1_waybel_0 @ X21 @ X20)))
% 26.70/26.89          | (r1_waybel_9 @ X21 @ X20)
% 26.70/26.89          | ~ (l1_orders_2 @ X21))),
% 26.70/26.89      inference('cnf', [status(esa)], [d3_waybel_9])).
% 26.70/26.89  thf('178', plain,
% 26.70/26.89      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | ~ (l1_orders_2 @ sk_A)
% 26.70/26.89        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['176', '177'])).
% 26.70/26.89  thf('179', plain, ((l1_orders_2 @ sk_A)),
% 26.70/26.89      inference('sup-', [status(thm)], ['110', '111'])).
% 26.70/26.89  thf('180', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('181', plain,
% 26.70/26.89      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (r1_waybel_9 @ sk_A @ sk_B))),
% 26.70/26.89      inference('demod', [status(thm)], ['178', '179', '180'])).
% 26.70/26.89  thf('182', plain,
% 26.70/26.89      (![X40 : $i]:
% 26.70/26.89         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X40) @ sk_A @ sk_A)
% 26.70/26.89          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('183', plain,
% 26.70/26.89      (((r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['181', '182'])).
% 26.70/26.89  thf('184', plain,
% 26.70/26.89      (((m1_subset_1 @ 
% 26.70/26.89         (sk_D @ 
% 26.70/26.89          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89          (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.89         (u1_struct_0 @ sk_A))
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['115'])).
% 26.70/26.89  thf('185', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (r2_lattice3 @ sk_A @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.89      inference('simplify', [status(thm)], ['102'])).
% 26.70/26.89  thf('186', plain,
% 26.70/26.89      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 26.70/26.89         ((zip_tseitin_0 @ X4 @ X5 @ X6 @ X7) | (r2_lattice3 @ X7 @ X5 @ X4))),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_6])).
% 26.70/26.89  thf('187', plain,
% 26.70/26.89      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 26.70/26.89         ((zip_tseitin_1 @ X8 @ X9 @ X10 @ X11)
% 26.70/26.89          | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X11))),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_1])).
% 26.70/26.89  thf('188', plain,
% 26.70/26.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 26.70/26.89         ((r2_lattice3 @ X0 @ X2 @ X3) | (zip_tseitin_1 @ X3 @ X2 @ X1 @ X0))),
% 26.70/26.89      inference('sup-', [status(thm)], ['186', '187'])).
% 26.70/26.89  thf('189', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | (zip_tseitin_2 @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | ~ (zip_tseitin_1 @ 
% 26.70/26.89               (sk_D @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ X0 @ 
% 26.70/26.89               (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.89      inference('demod', [status(thm)], ['108', '109', '112'])).
% 26.70/26.89  thf('190', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((r2_lattice3 @ sk_A @ X0 @ 
% 26.70/26.89           (sk_D @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89          | (zip_tseitin_2 @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['188', '189'])).
% 26.70/26.89  thf('191', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (r2_lattice3 @ sk_A @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (sk_D @ 
% 26.70/26.89            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)))),
% 26.70/26.89      inference('sup-', [status(thm)], ['185', '190'])).
% 26.70/26.89  thf('192', plain,
% 26.70/26.89      (((r2_lattice3 @ sk_A @ 
% 26.70/26.89         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89         (sk_D @ 
% 26.70/26.89          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89          (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['191'])).
% 26.70/26.89  thf('193', plain,
% 26.70/26.89      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 26.70/26.89         ((v2_struct_0 @ X27)
% 26.70/26.89          | ~ (v4_orders_2 @ X27)
% 26.70/26.89          | ~ (v7_waybel_0 @ X27)
% 26.70/26.89          | ~ (l1_waybel_0 @ X27 @ X28)
% 26.70/26.89          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 26.70/26.89          | ~ (r2_lattice3 @ X28 @ 
% 26.70/26.89               (k2_relset_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28) @ 
% 26.70/26.89                (u1_waybel_0 @ X28 @ X27)) @ 
% 26.70/26.89               X30)
% 26.70/26.89          | (r3_orders_2 @ X28 @ X29 @ X30)
% 26.70/26.89          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 26.70/26.89          | ((X31) != (X29))
% 26.70/26.89          | ~ (r3_waybel_9 @ X28 @ X27 @ X31)
% 26.70/26.89          | ~ (v5_pre_topc @ (k4_waybel_1 @ X28 @ (sk_E_1 @ X28)) @ X28 @ X28)
% 26.70/26.89          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X28))
% 26.70/26.89          | ~ (l1_waybel_9 @ X28)
% 26.70/26.89          | ~ (v1_compts_1 @ X28)
% 26.70/26.89          | ~ (v2_lattice3 @ X28)
% 26.70/26.89          | ~ (v1_lattice3 @ X28)
% 26.70/26.89          | ~ (v5_orders_2 @ X28)
% 26.70/26.89          | ~ (v4_orders_2 @ X28)
% 26.70/26.89          | ~ (v3_orders_2 @ X28)
% 26.70/26.89          | ~ (v8_pre_topc @ X28)
% 26.70/26.89          | ~ (v2_pre_topc @ X28))),
% 26.70/26.89      inference('cnf', [status(esa)], [l49_waybel_9])).
% 26.70/26.89  thf('194', plain,
% 26.70/26.89      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 26.70/26.89         (~ (v2_pre_topc @ X28)
% 26.70/26.89          | ~ (v8_pre_topc @ X28)
% 26.70/26.89          | ~ (v3_orders_2 @ X28)
% 26.70/26.89          | ~ (v4_orders_2 @ X28)
% 26.70/26.89          | ~ (v5_orders_2 @ X28)
% 26.70/26.89          | ~ (v1_lattice3 @ X28)
% 26.70/26.89          | ~ (v2_lattice3 @ X28)
% 26.70/26.89          | ~ (v1_compts_1 @ X28)
% 26.70/26.89          | ~ (l1_waybel_9 @ X28)
% 26.70/26.89          | ~ (v5_pre_topc @ (k4_waybel_1 @ X28 @ (sk_E_1 @ X28)) @ X28 @ X28)
% 26.70/26.89          | ~ (r3_waybel_9 @ X28 @ X27 @ X29)
% 26.70/26.89          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 26.70/26.89          | (r3_orders_2 @ X28 @ X29 @ X30)
% 26.70/26.89          | ~ (r2_lattice3 @ X28 @ 
% 26.70/26.89               (k2_relset_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28) @ 
% 26.70/26.89                (u1_waybel_0 @ X28 @ X27)) @ 
% 26.70/26.89               X30)
% 26.70/26.89          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 26.70/26.89          | ~ (l1_waybel_0 @ X27 @ X28)
% 26.70/26.89          | ~ (v7_waybel_0 @ X27)
% 26.70/26.89          | ~ (v4_orders_2 @ X27)
% 26.70/26.89          | (v2_struct_0 @ X27))),
% 26.70/26.89      inference('simplify', [status(thm)], ['193'])).
% 26.70/26.89  thf('195', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | (zip_tseitin_2 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | ~ (v4_orders_2 @ sk_B)
% 26.70/26.89          | ~ (v7_waybel_0 @ sk_B)
% 26.70/26.89          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 26.70/26.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (r3_orders_2 @ sk_A @ X0 @ 
% 26.70/26.89             (sk_D @ 
% 26.70/26.89              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89          | ~ (m1_subset_1 @ 
% 26.70/26.89               (sk_D @ 
% 26.70/26.89                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89                (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.89               (u1_struct_0 @ sk_A))
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 26.70/26.89          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 26.70/26.89               sk_A)
% 26.70/26.89          | ~ (l1_waybel_9 @ sk_A)
% 26.70/26.89          | ~ (v1_compts_1 @ sk_A)
% 26.70/26.89          | ~ (v2_lattice3 @ sk_A)
% 26.70/26.89          | ~ (v1_lattice3 @ sk_A)
% 26.70/26.89          | ~ (v5_orders_2 @ sk_A)
% 26.70/26.89          | ~ (v4_orders_2 @ sk_A)
% 26.70/26.89          | ~ (v3_orders_2 @ sk_A)
% 26.70/26.89          | ~ (v8_pre_topc @ sk_A)
% 26.70/26.89          | ~ (v2_pre_topc @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['192', '194'])).
% 26.70/26.89  thf('196', plain, ((v4_orders_2 @ sk_B)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('197', plain, ((v7_waybel_0 @ sk_B)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('198', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('199', plain, ((l1_waybel_9 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('200', plain, ((v1_compts_1 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('201', plain, ((v2_lattice3 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('202', plain, ((v1_lattice3 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('203', plain, ((v5_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('204', plain, ((v4_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('205', plain, ((v3_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('206', plain, ((v8_pre_topc @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('207', plain, ((v2_pre_topc @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('208', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | (zip_tseitin_2 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (r3_orders_2 @ sk_A @ X0 @ 
% 26.70/26.89             (sk_D @ 
% 26.70/26.89              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89          | ~ (m1_subset_1 @ 
% 26.70/26.89               (sk_D @ 
% 26.70/26.89                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89                (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.89               (u1_struct_0 @ sk_A))
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 26.70/26.89          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 26.70/26.89               sk_A))),
% 26.70/26.89      inference('demod', [status(thm)],
% 26.70/26.89                ['195', '196', '197', '198', '199', '200', '201', '202', 
% 26.70/26.89                 '203', '204', '205', '206', '207'])).
% 26.70/26.89  thf('209', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         (~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 26.70/26.89          | ~ (m1_subset_1 @ 
% 26.70/26.89               (sk_D @ 
% 26.70/26.89                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89                (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.89               (u1_struct_0 @ sk_A))
% 26.70/26.89          | (r3_orders_2 @ sk_A @ X0 @ 
% 26.70/26.89             (sk_D @ 
% 26.70/26.89              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (zip_tseitin_2 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['208'])).
% 26.70/26.89  thf('210', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | (zip_tseitin_2 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ sk_A)
% 26.70/26.89          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | (zip_tseitin_2 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (r3_orders_2 @ sk_A @ X0 @ 
% 26.70/26.89             (sk_D @ 
% 26.70/26.89              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 26.70/26.89          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 26.70/26.89               sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['184', '209'])).
% 26.70/26.89  thf('211', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         (~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 26.70/26.89          | (r3_orders_2 @ sk_A @ X0 @ 
% 26.70/26.89             (sk_D @ 
% 26.70/26.89              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (zip_tseitin_2 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['210'])).
% 26.70/26.89  thf('212', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_B)
% 26.70/26.89          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (v2_struct_0 @ sk_A)
% 26.70/26.89          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89          | (v2_struct_0 @ sk_A)
% 26.70/26.89          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | (zip_tseitin_2 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (r3_orders_2 @ sk_A @ X0 @ 
% 26.70/26.89             (sk_D @ 
% 26.70/26.89              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0))),
% 26.70/26.89      inference('sup-', [status(thm)], ['183', '211'])).
% 26.70/26.89  thf('213', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         (~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 26.70/26.89          | (r3_orders_2 @ sk_A @ X0 @ 
% 26.70/26.89             (sk_D @ 
% 26.70/26.89              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (zip_tseitin_2 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89          | (v2_struct_0 @ sk_A)
% 26.70/26.89          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (v2_struct_0 @ sk_B))),
% 26.70/26.89      inference('simplify', [status(thm)], ['212'])).
% 26.70/26.89  thf('214', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.89           (sk_D @ 
% 26.70/26.89            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)))),
% 26.70/26.89      inference('sup-', [status(thm)], ['118', '213'])).
% 26.70/26.89  thf('215', plain,
% 26.70/26.89      (((r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.89         (sk_D @ 
% 26.70/26.89          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89          (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['214'])).
% 26.70/26.89  thf('216', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.89           (sk_D @ 
% 26.70/26.89            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)))),
% 26.70/26.89      inference('sup-', [status(thm)], ['117', '215'])).
% 26.70/26.89  thf('217', plain,
% 26.70/26.89      (((r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.89         (sk_D @ 
% 26.70/26.89          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89          (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['216'])).
% 26.70/26.89  thf('218', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 26.70/26.89          | ~ (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 26.70/26.89          | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['160'])).
% 26.70/26.89  thf('219', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.89           (sk_D @ 
% 26.70/26.89            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89        | ~ (m1_subset_1 @ 
% 26.70/26.89             (sk_D @ 
% 26.70/26.89              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.89             (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('sup-', [status(thm)], ['217', '218'])).
% 26.70/26.89  thf('220', plain,
% 26.70/26.89      ((~ (m1_subset_1 @ 
% 26.70/26.89           (sk_D @ 
% 26.70/26.89            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.89           (u1_struct_0 @ sk_A))
% 26.70/26.89        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.89           (sk_D @ 
% 26.70/26.89            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['219'])).
% 26.70/26.89  thf('221', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.89           (sk_D @ 
% 26.70/26.89            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)))),
% 26.70/26.89      inference('sup-', [status(thm)], ['116', '220'])).
% 26.70/26.89  thf('222', plain,
% 26.70/26.89      (((r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.89         (sk_D @ 
% 26.70/26.89          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89          (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.89        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['221'])).
% 26.70/26.89  thf('223', plain,
% 26.70/26.89      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 26.70/26.89         ((zip_tseitin_0 @ X4 @ X5 @ X6 @ X7) | ~ (r1_orders_2 @ X7 @ X6 @ X4))),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_6])).
% 26.70/26.89  thf('224', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | (zip_tseitin_2 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89          | (zip_tseitin_0 @ 
% 26.70/26.89             (sk_D @ 
% 26.70/26.89              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.89             X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['222', '223'])).
% 26.70/26.89  thf('225', plain,
% 26.70/26.89      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 26.70/26.89         ((zip_tseitin_1 @ X8 @ X9 @ X10 @ X11)
% 26.70/26.89          | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X11))),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_1])).
% 26.70/26.89  thf('226', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89          | (zip_tseitin_2 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (v2_struct_0 @ sk_A)
% 26.70/26.89          | (zip_tseitin_1 @ 
% 26.70/26.89             (sk_D @ 
% 26.70/26.89              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.89             X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['224', '225'])).
% 26.70/26.89  thf('227', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | (zip_tseitin_2 @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | ~ (zip_tseitin_1 @ 
% 26.70/26.89               (sk_D @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ X0 @ 
% 26.70/26.89               (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.89      inference('demod', [status(thm)], ['108', '109', '112'])).
% 26.70/26.89  thf('228', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89        | ~ (r2_lattice3 @ sk_A @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89             (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['226', '227'])).
% 26.70/26.89  thf('229', plain,
% 26.70/26.89      ((~ (r2_lattice3 @ sk_A @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['228'])).
% 26.70/26.89  thf('230', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (r1_waybel_9 @ sk_A @ sk_B))),
% 26.70/26.89      inference('sup-', [status(thm)], ['103', '229'])).
% 26.70/26.89  thf('231', plain,
% 26.70/26.89      (((r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89        | (zip_tseitin_2 @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.89           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('simplify', [status(thm)], ['230'])).
% 26.70/26.89  thf('232', plain,
% 26.70/26.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 26.70/26.89         ((r1_yellow_0 @ X12 @ X13) | ~ (zip_tseitin_2 @ X13 @ X14 @ X12))),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_3])).
% 26.70/26.89  thf('233', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89        | (r1_yellow_0 @ sk_A @ 
% 26.70/26.89           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89            (u1_waybel_0 @ sk_A @ sk_B))))),
% 26.70/26.89      inference('sup-', [status(thm)], ['231', '232'])).
% 26.70/26.89  thf('234', plain,
% 26.70/26.89      (![X20 : $i, X21 : $i]:
% 26.70/26.89         (~ (l1_waybel_0 @ X20 @ X21)
% 26.70/26.89          | ~ (r1_yellow_0 @ X21 @ 
% 26.70/26.89               (k2_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21) @ 
% 26.70/26.89                (u1_waybel_0 @ X21 @ X20)))
% 26.70/26.89          | (r1_waybel_9 @ X21 @ X20)
% 26.70/26.89          | ~ (l1_orders_2 @ X21))),
% 26.70/26.89      inference('cnf', [status(esa)], [d3_waybel_9])).
% 26.70/26.89  thf('235', plain,
% 26.70/26.89      (((r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | ~ (l1_orders_2 @ sk_A)
% 26.70/26.89        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['233', '234'])).
% 26.70/26.89  thf('236', plain, ((l1_orders_2 @ sk_A)),
% 26.70/26.89      inference('sup-', [status(thm)], ['110', '111'])).
% 26.70/26.89  thf('237', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('238', plain,
% 26.70/26.89      (((r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (r1_waybel_9 @ sk_A @ sk_B))),
% 26.70/26.89      inference('demod', [status(thm)], ['235', '236', '237'])).
% 26.70/26.89  thf('239', plain,
% 26.70/26.89      (((v2_struct_0 @ sk_A)
% 26.70/26.89        | (m1_subset_1 @ (sk_E @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (r1_waybel_9 @ sk_A @ sk_B))),
% 26.70/26.89      inference('simplify', [status(thm)], ['238'])).
% 26.70/26.89  thf('240', plain,
% 26.70/26.89      (![X40 : $i]:
% 26.70/26.89         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X40) @ sk_A @ sk_A)
% 26.70/26.89          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ sk_A)))),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('241', plain,
% 26.70/26.89      (((r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_B)
% 26.70/26.89        | (v2_struct_0 @ sk_A)
% 26.70/26.89        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E @ sk_A)) @ sk_A @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['239', '240'])).
% 26.70/26.89  thf('242', plain,
% 26.70/26.89      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 26.70/26.89         ((v2_struct_0 @ X23)
% 26.70/26.89          | ~ (v4_orders_2 @ X23)
% 26.70/26.89          | ~ (v7_waybel_0 @ X23)
% 26.70/26.89          | ~ (l1_waybel_0 @ X23 @ X24)
% 26.70/26.89          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 26.70/26.89          | (r2_lattice3 @ X24 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24) @ 
% 26.70/26.89              (u1_waybel_0 @ X24 @ X23)) @ 
% 26.70/26.89             X25)
% 26.70/26.89          | ((X26) != (X25))
% 26.70/26.89          | ~ (r3_waybel_9 @ X24 @ X23 @ X26)
% 26.70/26.89          | ~ (v10_waybel_0 @ X23 @ X24)
% 26.70/26.89          | ~ (v5_pre_topc @ (k4_waybel_1 @ X24 @ (sk_E @ X24)) @ X24 @ X24)
% 26.70/26.89          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 26.70/26.89          | ~ (l1_waybel_9 @ X24)
% 26.70/26.89          | ~ (v1_compts_1 @ X24)
% 26.70/26.89          | ~ (v2_lattice3 @ X24)
% 26.70/26.89          | ~ (v1_lattice3 @ X24)
% 26.70/26.89          | ~ (v5_orders_2 @ X24)
% 26.70/26.89          | ~ (v4_orders_2 @ X24)
% 26.70/26.89          | ~ (v3_orders_2 @ X24)
% 26.70/26.89          | ~ (v8_pre_topc @ X24)
% 26.70/26.89          | ~ (v2_pre_topc @ X24))),
% 26.70/26.89      inference('cnf', [status(esa)], [l48_waybel_9])).
% 26.70/26.89  thf('243', plain,
% 26.70/26.89      (![X23 : $i, X24 : $i, X25 : $i]:
% 26.70/26.89         (~ (v2_pre_topc @ X24)
% 26.70/26.89          | ~ (v8_pre_topc @ X24)
% 26.70/26.89          | ~ (v3_orders_2 @ X24)
% 26.70/26.89          | ~ (v4_orders_2 @ X24)
% 26.70/26.89          | ~ (v5_orders_2 @ X24)
% 26.70/26.89          | ~ (v1_lattice3 @ X24)
% 26.70/26.89          | ~ (v2_lattice3 @ X24)
% 26.70/26.89          | ~ (v1_compts_1 @ X24)
% 26.70/26.89          | ~ (l1_waybel_9 @ X24)
% 26.70/26.89          | ~ (v5_pre_topc @ (k4_waybel_1 @ X24 @ (sk_E @ X24)) @ X24 @ X24)
% 26.70/26.89          | ~ (v10_waybel_0 @ X23 @ X24)
% 26.70/26.89          | ~ (r3_waybel_9 @ X24 @ X23 @ X25)
% 26.70/26.89          | (r2_lattice3 @ X24 @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24) @ 
% 26.70/26.89              (u1_waybel_0 @ X24 @ X23)) @ 
% 26.70/26.89             X25)
% 26.70/26.89          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 26.70/26.89          | ~ (l1_waybel_0 @ X23 @ X24)
% 26.70/26.89          | ~ (v7_waybel_0 @ X23)
% 26.70/26.89          | ~ (v4_orders_2 @ X23)
% 26.70/26.89          | (v2_struct_0 @ X23))),
% 26.70/26.89      inference('simplify', [status(thm)], ['242'])).
% 26.70/26.89  thf('244', plain,
% 26.70/26.89      (![X0 : $i, X1 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89          | (v2_struct_0 @ X0)
% 26.70/26.89          | ~ (v4_orders_2 @ X0)
% 26.70/26.89          | ~ (v7_waybel_0 @ X0)
% 26.70/26.89          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (r2_lattice3 @ sk_A @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ X0)) @ 
% 26.70/26.89             X1)
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 26.70/26.89          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | ~ (l1_waybel_9 @ sk_A)
% 26.70/26.89          | ~ (v1_compts_1 @ sk_A)
% 26.70/26.89          | ~ (v2_lattice3 @ sk_A)
% 26.70/26.89          | ~ (v1_lattice3 @ sk_A)
% 26.70/26.89          | ~ (v5_orders_2 @ sk_A)
% 26.70/26.89          | ~ (v4_orders_2 @ sk_A)
% 26.70/26.89          | ~ (v3_orders_2 @ sk_A)
% 26.70/26.89          | ~ (v8_pre_topc @ sk_A)
% 26.70/26.89          | ~ (v2_pre_topc @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['241', '243'])).
% 26.70/26.89  thf('245', plain, ((l1_waybel_9 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('246', plain, ((v1_compts_1 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('247', plain, ((v2_lattice3 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('248', plain, ((v1_lattice3 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('249', plain, ((v5_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('250', plain, ((v4_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('251', plain, ((v3_orders_2 @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('252', plain, ((v8_pre_topc @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('253', plain, ((v2_pre_topc @ sk_A)),
% 26.70/26.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.89  thf('254', plain,
% 26.70/26.89      (![X0 : $i, X1 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89          | (v2_struct_0 @ X0)
% 26.70/26.89          | ~ (v4_orders_2 @ X0)
% 26.70/26.89          | ~ (v7_waybel_0 @ X0)
% 26.70/26.89          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 26.70/26.89          | (r2_lattice3 @ sk_A @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ X0)) @ 
% 26.70/26.89             X1)
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 26.70/26.89          | ~ (v10_waybel_0 @ X0 @ sk_A))),
% 26.70/26.89      inference('demod', [status(thm)],
% 26.70/26.89                ['244', '245', '246', '247', '248', '249', '250', '251', 
% 26.70/26.89                 '252', '253'])).
% 26.70/26.89  thf('255', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_A)
% 26.70/26.89          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89          | (r2_lattice3 @ sk_A @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ X0)) @ 
% 26.70/26.89             (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | ~ (v7_waybel_0 @ X0)
% 26.70/26.89          | ~ (v4_orders_2 @ X0)
% 26.70/26.89          | (v2_struct_0 @ X0)
% 26.70/26.89          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89          | (v2_struct_0 @ sk_B)
% 26.70/26.89          | (v2_struct_0 @ sk_A))),
% 26.70/26.89      inference('sup-', [status(thm)], ['78', '254'])).
% 26.70/26.89  thf('256', plain,
% 26.70/26.89      (![X0 : $i]:
% 26.70/26.89         ((v2_struct_0 @ sk_B)
% 26.70/26.89          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.89          | (v2_struct_0 @ X0)
% 26.70/26.89          | ~ (v4_orders_2 @ X0)
% 26.70/26.89          | ~ (v7_waybel_0 @ X0)
% 26.70/26.89          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.89          | (r2_lattice3 @ sk_A @ 
% 26.70/26.89             (k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.89              (u1_waybel_0 @ sk_A @ X0)) @ 
% 26.70/26.89             (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.89          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90          | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['255'])).
% 26.70/26.90  thf('257', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | ~ (v10_waybel_0 @ sk_B @ sk_A)
% 26.70/26.90        | (r2_lattice3 @ sk_A @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 26.70/26.90        | ~ (v7_waybel_0 @ sk_B)
% 26.70/26.90        | ~ (v4_orders_2 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B))),
% 26.70/26.90      inference('sup-', [status(thm)], ['74', '256'])).
% 26.70/26.90  thf('258', plain, ((v10_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('259', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('260', plain, ((v7_waybel_0 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('261', plain, ((v4_orders_2 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('262', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (r2_lattice3 @ sk_A @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B))),
% 26.70/26.90      inference('demod', [status(thm)], ['257', '258', '259', '260', '261'])).
% 26.70/26.90  thf('263', plain,
% 26.70/26.90      (((r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r2_lattice3 @ sk_A @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['262'])).
% 26.70/26.90  thf('264', plain,
% 26.70/26.90      (((r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r2_lattice3 @ sk_A @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['262'])).
% 26.70/26.90  thf('265', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((m1_subset_1 @ (sk_D @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.90           (u1_struct_0 @ sk_A))
% 26.70/26.90          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90          | (zip_tseitin_2 @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('sup-', [status(thm)], ['105', '113'])).
% 26.70/26.90  thf('266', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (m1_subset_1 @ 
% 26.70/26.90           (sk_D @ 
% 26.70/26.90            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.90           (u1_struct_0 @ sk_A)))),
% 26.70/26.90      inference('sup-', [status(thm)], ['264', '265'])).
% 26.70/26.90  thf('267', plain,
% 26.70/26.90      (((m1_subset_1 @ 
% 26.70/26.90         (sk_D @ 
% 26.70/26.90          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90          (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.90         (u1_struct_0 @ sk_A))
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['266'])).
% 26.70/26.90  thf('268', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 26.70/26.90      inference('simplify', [status(thm)], ['77'])).
% 26.70/26.90  thf('269', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.90      inference('simplify', [status(thm)], ['73'])).
% 26.70/26.90  thf('270', plain,
% 26.70/26.90      (((r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r2_lattice3 @ sk_A @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['262'])).
% 26.70/26.90  thf('271', plain,
% 26.70/26.90      (((m1_subset_1 @ 
% 26.70/26.90         (sk_D @ 
% 26.70/26.90          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90          (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.90         (u1_struct_0 @ sk_A))
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['266'])).
% 26.70/26.90  thf('272', plain,
% 26.70/26.90      (((r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r2_lattice3 @ sk_A @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['262'])).
% 26.70/26.90  thf('273', plain,
% 26.70/26.90      (((zip_tseitin_2 @ 
% 26.70/26.90         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90         (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | ~ (r2_lattice3 @ sk_A @ 
% 26.70/26.90             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90             (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (sk_D @ 
% 26.70/26.90            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 26.70/26.90      inference('simplify', [status(thm)], ['151'])).
% 26.70/26.90  thf('274', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (sk_D @ 
% 26.70/26.90            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))),
% 26.70/26.90      inference('sup-', [status(thm)], ['272', '273'])).
% 26.70/26.90  thf('275', plain,
% 26.70/26.90      (((zip_tseitin_2 @ 
% 26.70/26.90         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90         (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (sk_D @ 
% 26.70/26.90            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['274'])).
% 26.70/26.90  thf('276', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.90          | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 26.70/26.90          | ~ (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 26.70/26.90          | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['160'])).
% 26.70/26.90  thf('277', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (sk_D @ 
% 26.70/26.90            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90        | ~ (m1_subset_1 @ 
% 26.70/26.90             (sk_D @ 
% 26.70/26.90              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.90             (u1_struct_0 @ sk_A)))),
% 26.70/26.90      inference('sup-', [status(thm)], ['275', '276'])).
% 26.70/26.90  thf('278', plain,
% 26.70/26.90      ((~ (m1_subset_1 @ 
% 26.70/26.90           (sk_D @ 
% 26.70/26.90            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.90           (u1_struct_0 @ sk_A))
% 26.70/26.90        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (sk_D @ 
% 26.70/26.90            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['277'])).
% 26.70/26.90  thf('279', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (sk_D @ 
% 26.70/26.90            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)))),
% 26.70/26.90      inference('sup-', [status(thm)], ['271', '278'])).
% 26.70/26.90  thf('280', plain,
% 26.70/26.90      (((r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90         (sk_D @ 
% 26.70/26.90          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90          (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['279'])).
% 26.70/26.90  thf('281', plain,
% 26.70/26.90      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 26.70/26.90         ((zip_tseitin_0 @ X4 @ X5 @ X6 @ X7) | ~ (r1_orders_2 @ X7 @ X6 @ X4))),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_6])).
% 26.70/26.90  thf('282', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_B)
% 26.70/26.90          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90          | (zip_tseitin_2 @ 
% 26.70/26.90             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90          | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90          | (zip_tseitin_0 @ 
% 26.70/26.90             (sk_D @ 
% 26.70/26.90              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.90             X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))),
% 26.70/26.90      inference('sup-', [status(thm)], ['280', '281'])).
% 26.70/26.90  thf('283', plain,
% 26.70/26.90      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 26.70/26.90         ((zip_tseitin_1 @ X8 @ X9 @ X10 @ X11)
% 26.70/26.90          | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X11))),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_1])).
% 26.70/26.90  thf('284', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90          | (zip_tseitin_2 @ 
% 26.70/26.90             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90          | (v2_struct_0 @ sk_B)
% 26.70/26.90          | (v2_struct_0 @ sk_A)
% 26.70/26.90          | (zip_tseitin_1 @ 
% 26.70/26.90             (sk_D @ 
% 26.70/26.90              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.90             X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))),
% 26.70/26.90      inference('sup-', [status(thm)], ['282', '283'])).
% 26.70/26.90  thf('285', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ sk_A)
% 26.70/26.90          | (zip_tseitin_2 @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90          | ~ (zip_tseitin_1 @ 
% 26.70/26.90               (sk_D @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ X0 @ 
% 26.70/26.90               (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.90      inference('demod', [status(thm)], ['108', '109', '112'])).
% 26.70/26.90  thf('286', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | ~ (r2_lattice3 @ sk_A @ 
% 26.70/26.90             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90             (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('sup-', [status(thm)], ['284', '285'])).
% 26.70/26.90  thf('287', plain,
% 26.70/26.90      ((~ (r2_lattice3 @ sk_A @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['286'])).
% 26.70/26.90  thf('288', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 26.70/26.90      inference('sup-', [status(thm)], ['270', '287'])).
% 26.70/26.90  thf('289', plain,
% 26.70/26.90      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['288'])).
% 26.70/26.90  thf('290', plain,
% 26.70/26.90      (![X12 : $i, X13 : $i, X14 : $i]:
% 26.70/26.90         ((r1_yellow_0 @ X12 @ X13) | ~ (zip_tseitin_2 @ X13 @ X14 @ X12))),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_3])).
% 26.70/26.90  thf('291', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (r1_yellow_0 @ sk_A @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['289', '290'])).
% 26.70/26.90  thf('292', plain,
% 26.70/26.90      (![X20 : $i, X21 : $i]:
% 26.70/26.90         (~ (l1_waybel_0 @ X20 @ X21)
% 26.70/26.90          | ~ (r1_yellow_0 @ X21 @ 
% 26.70/26.90               (k2_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21) @ 
% 26.70/26.90                (u1_waybel_0 @ X21 @ X20)))
% 26.70/26.90          | (r1_waybel_9 @ X21 @ X20)
% 26.70/26.90          | ~ (l1_orders_2 @ X21))),
% 26.70/26.90      inference('cnf', [status(esa)], [d3_waybel_9])).
% 26.70/26.90  thf('293', plain,
% 26.70/26.90      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | ~ (l1_orders_2 @ sk_A)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 26.70/26.90      inference('sup-', [status(thm)], ['291', '292'])).
% 26.70/26.90  thf('294', plain, ((l1_orders_2 @ sk_A)),
% 26.70/26.90      inference('sup-', [status(thm)], ['110', '111'])).
% 26.70/26.90  thf('295', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('296', plain,
% 26.70/26.90      (((m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B))),
% 26.70/26.90      inference('demod', [status(thm)], ['293', '294', '295'])).
% 26.70/26.90  thf('297', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (m1_subset_1 @ (sk_E_1 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 26.70/26.90      inference('simplify', [status(thm)], ['296'])).
% 26.70/26.90  thf('298', plain,
% 26.70/26.90      (![X40 : $i]:
% 26.70/26.90         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X40) @ sk_A @ sk_A)
% 26.70/26.90          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ sk_A)))),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('299', plain,
% 26.70/26.90      (((r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A))),
% 26.70/26.90      inference('sup-', [status(thm)], ['297', '298'])).
% 26.70/26.90  thf('300', plain,
% 26.70/26.90      (((m1_subset_1 @ 
% 26.70/26.90         (sk_D @ 
% 26.70/26.90          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90          (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.90         (u1_struct_0 @ sk_A))
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['266'])).
% 26.70/26.90  thf('301', plain,
% 26.70/26.90      (((r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r2_lattice3 @ sk_A @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['262'])).
% 26.70/26.90  thf('302', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((r2_lattice3 @ sk_A @ X0 @ 
% 26.70/26.90           (sk_D @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90          | (zip_tseitin_2 @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('sup-', [status(thm)], ['188', '189'])).
% 26.70/26.90  thf('303', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (r2_lattice3 @ sk_A @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (sk_D @ 
% 26.70/26.90            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)))),
% 26.70/26.90      inference('sup-', [status(thm)], ['301', '302'])).
% 26.70/26.90  thf('304', plain,
% 26.70/26.90      (((r2_lattice3 @ sk_A @ 
% 26.70/26.90         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90         (sk_D @ 
% 26.70/26.90          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90          (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['303'])).
% 26.70/26.90  thf('305', plain,
% 26.70/26.90      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 26.70/26.90         (~ (v2_pre_topc @ X28)
% 26.70/26.90          | ~ (v8_pre_topc @ X28)
% 26.70/26.90          | ~ (v3_orders_2 @ X28)
% 26.70/26.90          | ~ (v4_orders_2 @ X28)
% 26.70/26.90          | ~ (v5_orders_2 @ X28)
% 26.70/26.90          | ~ (v1_lattice3 @ X28)
% 26.70/26.90          | ~ (v2_lattice3 @ X28)
% 26.70/26.90          | ~ (v1_compts_1 @ X28)
% 26.70/26.90          | ~ (l1_waybel_9 @ X28)
% 26.70/26.90          | ~ (v5_pre_topc @ (k4_waybel_1 @ X28 @ (sk_E_1 @ X28)) @ X28 @ X28)
% 26.70/26.90          | ~ (r3_waybel_9 @ X28 @ X27 @ X29)
% 26.70/26.90          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 26.70/26.90          | (r3_orders_2 @ X28 @ X29 @ X30)
% 26.70/26.90          | ~ (r2_lattice3 @ X28 @ 
% 26.70/26.90               (k2_relset_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X28) @ 
% 26.70/26.90                (u1_waybel_0 @ X28 @ X27)) @ 
% 26.70/26.90               X30)
% 26.70/26.90          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 26.70/26.90          | ~ (l1_waybel_0 @ X27 @ X28)
% 26.70/26.90          | ~ (v7_waybel_0 @ X27)
% 26.70/26.90          | ~ (v4_orders_2 @ X27)
% 26.70/26.90          | (v2_struct_0 @ X27))),
% 26.70/26.90      inference('simplify', [status(thm)], ['193'])).
% 26.70/26.90  thf('306', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_B)
% 26.70/26.90          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90          | (zip_tseitin_2 @ 
% 26.70/26.90             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_B)
% 26.70/26.90          | ~ (v4_orders_2 @ sk_B)
% 26.70/26.90          | ~ (v7_waybel_0 @ sk_B)
% 26.70/26.90          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 26.70/26.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.90          | (r3_orders_2 @ sk_A @ X0 @ 
% 26.70/26.90             (sk_D @ 
% 26.70/26.90              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90          | ~ (m1_subset_1 @ 
% 26.70/26.90               (sk_D @ 
% 26.70/26.90                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90                (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.90               (u1_struct_0 @ sk_A))
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 26.70/26.90          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 26.70/26.90               sk_A)
% 26.70/26.90          | ~ (l1_waybel_9 @ sk_A)
% 26.70/26.90          | ~ (v1_compts_1 @ sk_A)
% 26.70/26.90          | ~ (v2_lattice3 @ sk_A)
% 26.70/26.90          | ~ (v1_lattice3 @ sk_A)
% 26.70/26.90          | ~ (v5_orders_2 @ sk_A)
% 26.70/26.90          | ~ (v4_orders_2 @ sk_A)
% 26.70/26.90          | ~ (v3_orders_2 @ sk_A)
% 26.70/26.90          | ~ (v8_pre_topc @ sk_A)
% 26.70/26.90          | ~ (v2_pre_topc @ sk_A))),
% 26.70/26.90      inference('sup-', [status(thm)], ['304', '305'])).
% 26.70/26.90  thf('307', plain, ((v4_orders_2 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('308', plain, ((v7_waybel_0 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('309', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('310', plain, ((l1_waybel_9 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('311', plain, ((v1_compts_1 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('312', plain, ((v2_lattice3 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('313', plain, ((v1_lattice3 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('314', plain, ((v5_orders_2 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('315', plain, ((v4_orders_2 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('316', plain, ((v3_orders_2 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('317', plain, ((v8_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('318', plain, ((v2_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('319', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_B)
% 26.70/26.90          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90          | (zip_tseitin_2 @ 
% 26.70/26.90             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_B)
% 26.70/26.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.90          | (r3_orders_2 @ sk_A @ X0 @ 
% 26.70/26.90             (sk_D @ 
% 26.70/26.90              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90          | ~ (m1_subset_1 @ 
% 26.70/26.90               (sk_D @ 
% 26.70/26.90                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90                (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.90               (u1_struct_0 @ sk_A))
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 26.70/26.90          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 26.70/26.90               sk_A))),
% 26.70/26.90      inference('demod', [status(thm)],
% 26.70/26.90                ['306', '307', '308', '309', '310', '311', '312', '313', 
% 26.70/26.90                 '314', '315', '316', '317', '318'])).
% 26.70/26.90  thf('320', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         (~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 26.70/26.90          | ~ (m1_subset_1 @ 
% 26.70/26.90               (sk_D @ 
% 26.70/26.90                (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90                 (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90                (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.90               (u1_struct_0 @ sk_A))
% 26.70/26.90          | (r3_orders_2 @ sk_A @ X0 @ 
% 26.70/26.90             (sk_D @ 
% 26.70/26.90              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.90          | (zip_tseitin_2 @ 
% 26.70/26.90             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90          | (v2_struct_0 @ sk_B)
% 26.70/26.90          | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['319'])).
% 26.70/26.90  thf('321', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_B)
% 26.70/26.90          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90          | (zip_tseitin_2 @ 
% 26.70/26.90             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_B)
% 26.70/26.90          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90          | (zip_tseitin_2 @ 
% 26.70/26.90             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.90          | (r3_orders_2 @ sk_A @ X0 @ 
% 26.70/26.90             (sk_D @ 
% 26.70/26.90              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 26.70/26.90          | ~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ 
% 26.70/26.90               sk_A))),
% 26.70/26.90      inference('sup-', [status(thm)], ['300', '320'])).
% 26.70/26.90  thf('322', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         (~ (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_E_1 @ sk_A)) @ sk_A @ sk_A)
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 26.70/26.90          | (r3_orders_2 @ sk_A @ X0 @ 
% 26.70/26.90             (sk_D @ 
% 26.70/26.90              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.90          | (zip_tseitin_2 @ 
% 26.70/26.90             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90          | (v2_struct_0 @ sk_B)
% 26.70/26.90          | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['321'])).
% 26.70/26.90  thf('323', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_B)
% 26.70/26.90          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90          | (v2_struct_0 @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_B)
% 26.70/26.90          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90          | (zip_tseitin_2 @ 
% 26.70/26.90             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.90          | (r3_orders_2 @ sk_A @ X0 @ 
% 26.70/26.90             (sk_D @ 
% 26.70/26.90              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ sk_B @ X0))),
% 26.70/26.90      inference('sup-', [status(thm)], ['299', '322'])).
% 26.70/26.90  thf('324', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         (~ (r3_waybel_9 @ sk_A @ sk_B @ X0)
% 26.70/26.90          | (r3_orders_2 @ sk_A @ X0 @ 
% 26.70/26.90             (sk_D @ 
% 26.70/26.90              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.90          | (zip_tseitin_2 @ 
% 26.70/26.90             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90          | (v2_struct_0 @ sk_B)
% 26.70/26.90          | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['323'])).
% 26.70/26.90  thf('325', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (sk_D @ 
% 26.70/26.90            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)))),
% 26.70/26.90      inference('sup-', [status(thm)], ['269', '324'])).
% 26.70/26.90  thf('326', plain,
% 26.70/26.90      (((r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90         (sk_D @ 
% 26.70/26.90          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90          (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90        | ~ (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['325'])).
% 26.70/26.90  thf('327', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (sk_D @ 
% 26.70/26.90            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)))),
% 26.70/26.90      inference('sup-', [status(thm)], ['268', '326'])).
% 26.70/26.90  thf('328', plain,
% 26.70/26.90      (((r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90         (sk_D @ 
% 26.70/26.90          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90          (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['327'])).
% 26.70/26.90  thf('329', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 26.70/26.90          | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 26.70/26.90          | ~ (r3_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ X0)
% 26.70/26.90          | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['160'])).
% 26.70/26.90  thf('330', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (sk_D @ 
% 26.70/26.90            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90        | ~ (m1_subset_1 @ 
% 26.70/26.90             (sk_D @ 
% 26.70/26.90              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.90             (u1_struct_0 @ sk_A)))),
% 26.70/26.90      inference('sup-', [status(thm)], ['328', '329'])).
% 26.70/26.90  thf('331', plain,
% 26.70/26.90      ((~ (m1_subset_1 @ 
% 26.70/26.90           (sk_D @ 
% 26.70/26.90            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.90           (u1_struct_0 @ sk_A))
% 26.70/26.90        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (sk_D @ 
% 26.70/26.90            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['330'])).
% 26.70/26.90  thf('332', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (sk_D @ 
% 26.70/26.90            (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90             (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90            (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)))),
% 26.70/26.90      inference('sup-', [status(thm)], ['267', '331'])).
% 26.70/26.90  thf('333', plain,
% 26.70/26.90      (((r1_orders_2 @ sk_A @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90         (sk_D @ 
% 26.70/26.90          (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90           (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90          (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['332'])).
% 26.70/26.90  thf('334', plain,
% 26.70/26.90      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 26.70/26.90         ((zip_tseitin_0 @ X4 @ X5 @ X6 @ X7) | ~ (r1_orders_2 @ X7 @ X6 @ X4))),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_6])).
% 26.70/26.90  thf('335', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_B)
% 26.70/26.90          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90          | (zip_tseitin_2 @ 
% 26.70/26.90             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90             (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90          | (zip_tseitin_0 @ 
% 26.70/26.90             (sk_D @ 
% 26.70/26.90              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.90             X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))),
% 26.70/26.90      inference('sup-', [status(thm)], ['333', '334'])).
% 26.70/26.90  thf('336', plain,
% 26.70/26.90      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 26.70/26.90         ((zip_tseitin_1 @ X8 @ X9 @ X10 @ X11)
% 26.70/26.90          | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X11))),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_1])).
% 26.70/26.90  thf('337', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90          | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90          | (v2_struct_0 @ sk_B)
% 26.70/26.90          | (v2_struct_0 @ sk_A)
% 26.70/26.90          | (zip_tseitin_1 @ 
% 26.70/26.90             (sk_D @ 
% 26.70/26.90              (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90               (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90              (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ 
% 26.70/26.90             X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))),
% 26.70/26.90      inference('sup-', [status(thm)], ['335', '336'])).
% 26.70/26.90  thf('338', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ sk_A)
% 26.70/26.90          | (zip_tseitin_2 @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90          | ~ (zip_tseitin_1 @ 
% 26.70/26.90               (sk_D @ X0 @ (k1_waybel_2 @ sk_A @ sk_B) @ sk_A) @ X0 @ 
% 26.70/26.90               (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90          | ~ (r2_lattice3 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.90      inference('demod', [status(thm)], ['108', '109', '112'])).
% 26.70/26.90  thf('339', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | ~ (r2_lattice3 @ sk_A @ 
% 26.70/26.90             (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90              (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90             (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('sup-', [status(thm)], ['337', '338'])).
% 26.70/26.90  thf('340', plain,
% 26.70/26.90      ((~ (r2_lattice3 @ sk_A @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['339'])).
% 26.70/26.90  thf('341', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (zip_tseitin_2 @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90           (k1_waybel_2 @ sk_A @ sk_B) @ sk_A))),
% 26.70/26.90      inference('sup-', [status(thm)], ['263', '340'])).
% 26.70/26.90  thf('342', plain,
% 26.70/26.90      (((zip_tseitin_2 @ 
% 26.70/26.90         (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90          (u1_waybel_0 @ sk_A @ sk_B)) @ 
% 26.70/26.90         (k1_waybel_2 @ sk_A @ sk_B) @ sk_A)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['341'])).
% 26.70/26.90  thf('343', plain,
% 26.70/26.90      (![X12 : $i, X13 : $i, X14 : $i]:
% 26.70/26.90         ((r1_yellow_0 @ X12 @ X13) | ~ (zip_tseitin_2 @ X13 @ X14 @ X12))),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_3])).
% 26.70/26.90  thf('344', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (r1_yellow_0 @ sk_A @ 
% 26.70/26.90           (k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 26.70/26.90            (u1_waybel_0 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['342', '343'])).
% 26.70/26.90  thf('345', plain,
% 26.70/26.90      (![X20 : $i, X21 : $i]:
% 26.70/26.90         (~ (l1_waybel_0 @ X20 @ X21)
% 26.70/26.90          | ~ (r1_yellow_0 @ X21 @ 
% 26.70/26.90               (k2_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21) @ 
% 26.70/26.90                (u1_waybel_0 @ X21 @ X20)))
% 26.70/26.90          | (r1_waybel_9 @ X21 @ X20)
% 26.70/26.90          | ~ (l1_orders_2 @ X21))),
% 26.70/26.90      inference('cnf', [status(esa)], [d3_waybel_9])).
% 26.70/26.90  thf('346', plain,
% 26.70/26.90      (((r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | ~ (l1_orders_2 @ sk_A)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 26.70/26.90      inference('sup-', [status(thm)], ['344', '345'])).
% 26.70/26.90  thf('347', plain, ((l1_orders_2 @ sk_A)),
% 26.70/26.90      inference('sup-', [status(thm)], ['110', '111'])).
% 26.70/26.90  thf('348', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('349', plain,
% 26.70/26.90      (((r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B))),
% 26.70/26.90      inference('demod', [status(thm)], ['346', '347', '348'])).
% 26.70/26.90  thf('350', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_B)
% 26.70/26.90        | (r1_waybel_9 @ sk_A @ sk_B))),
% 26.70/26.90      inference('simplify', [status(thm)], ['349'])).
% 26.70/26.90  thf('351', plain, (~ (v2_struct_0 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('352', plain, (((r1_waybel_9 @ sk_A @ sk_B) | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('clc', [status(thm)], ['350', '351'])).
% 26.70/26.90  thf('353', plain,
% 26.70/26.90      ((~ (r1_waybel_9 @ sk_A @ sk_B)
% 26.70/26.90        | ~ (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90             (k10_yellow_6 @ sk_A @ sk_B)))),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('354', plain,
% 26.70/26.90      ((~ (r1_waybel_9 @ sk_A @ sk_B)) <= (~ ((r1_waybel_9 @ sk_A @ sk_B)))),
% 26.70/26.90      inference('split', [status(esa)], ['353'])).
% 26.70/26.90  thf('355', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.90      inference('clc', [status(thm)], ['69', '70'])).
% 26.70/26.90  thf('356', plain,
% 26.70/26.90      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('clc', [status(thm)], ['11', '12'])).
% 26.70/26.90  thf('357', plain,
% 26.70/26.90      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('clc', [status(thm)], ['23', '24'])).
% 26.70/26.90  thf(t33_waybel_9, axiom,
% 26.70/26.90    (![A:$i]:
% 26.70/26.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 26.70/26.90         ( v8_pre_topc @ A ) & ( v1_compts_1 @ A ) & ( l1_pre_topc @ A ) ) =>
% 26.70/26.90       ( ![B:$i]:
% 26.70/26.90         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 26.70/26.90             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 26.70/26.90           ( ( ![C:$i]:
% 26.70/26.90               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.90                 ( ![D:$i]:
% 26.70/26.90                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.90                     ( ( ( r3_waybel_9 @ A @ B @ C ) & 
% 26.70/26.90                         ( r3_waybel_9 @ A @ B @ D ) ) =>
% 26.70/26.90                       ( ( C ) = ( D ) ) ) ) ) ) ) =>
% 26.70/26.90             ( ![C:$i]:
% 26.70/26.90               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 26.70/26.90                 ( ( r3_waybel_9 @ A @ B @ C ) =>
% 26.70/26.90                   ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ) ))).
% 26.70/26.90  thf('358', plain,
% 26.70/26.90      (![X34 : $i, X35 : $i, X36 : $i]:
% 26.70/26.90         ((v2_struct_0 @ X34)
% 26.70/26.90          | ~ (v4_orders_2 @ X34)
% 26.70/26.90          | ~ (v7_waybel_0 @ X34)
% 26.70/26.90          | ~ (l1_waybel_0 @ X34 @ X35)
% 26.70/26.90          | ~ (r3_waybel_9 @ X35 @ X34 @ X36)
% 26.70/26.90          | (r2_hidden @ X36 @ (k10_yellow_6 @ X35 @ X34))
% 26.70/26.90          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 26.70/26.90          | (r3_waybel_9 @ X35 @ X34 @ (sk_C_1 @ X34 @ X35))
% 26.70/26.90          | ~ (l1_pre_topc @ X35)
% 26.70/26.90          | ~ (v1_compts_1 @ X35)
% 26.70/26.90          | ~ (v8_pre_topc @ X35)
% 26.70/26.90          | ~ (v2_pre_topc @ X35)
% 26.70/26.90          | (v2_struct_0 @ X35))),
% 26.70/26.90      inference('cnf', [status(esa)], [t33_waybel_9])).
% 26.70/26.90  thf('359', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_A)
% 26.70/26.90          | ~ (v2_pre_topc @ sk_A)
% 26.70/26.90          | ~ (v8_pre_topc @ sk_A)
% 26.70/26.90          | ~ (v1_compts_1 @ sk_A)
% 26.70/26.90          | ~ (l1_pre_topc @ sk_A)
% 26.70/26.90          | (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ X0 @ sk_A))
% 26.70/26.90          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 26.70/26.90          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90          | ~ (v7_waybel_0 @ X0)
% 26.70/26.90          | ~ (v4_orders_2 @ X0)
% 26.70/26.90          | (v2_struct_0 @ X0))),
% 26.70/26.90      inference('sup-', [status(thm)], ['357', '358'])).
% 26.70/26.90  thf('360', plain, ((v2_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('361', plain, ((v8_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('362', plain, ((v1_compts_1 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('363', plain, ((l1_pre_topc @ sk_A)),
% 26.70/26.90      inference('sup-', [status(thm)], ['6', '7'])).
% 26.70/26.90  thf('364', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_A)
% 26.70/26.90          | (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ X0 @ sk_A))
% 26.70/26.90          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 26.70/26.90          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90          | ~ (v7_waybel_0 @ X0)
% 26.70/26.90          | ~ (v4_orders_2 @ X0)
% 26.70/26.90          | (v2_struct_0 @ X0))),
% 26.70/26.90      inference('demod', [status(thm)], ['359', '360', '361', '362', '363'])).
% 26.70/26.90  thf('365', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ X0)
% 26.70/26.90          | ~ (v4_orders_2 @ X0)
% 26.70/26.90          | ~ (v7_waybel_0 @ X0)
% 26.70/26.90          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 26.70/26.90          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 26.70/26.90          | (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ X0 @ sk_A))
% 26.70/26.90          | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['364'])).
% 26.70/26.90  thf('366', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 26.70/26.90        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 26.70/26.90        | ~ (v7_waybel_0 @ sk_B)
% 26.70/26.90        | ~ (v4_orders_2 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B))),
% 26.70/26.90      inference('sup-', [status(thm)], ['356', '365'])).
% 26.70/26.90  thf('367', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('368', plain, ((v7_waybel_0 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('369', plain, ((v4_orders_2 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('370', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 26.70/26.90        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90        | (v2_struct_0 @ sk_B))),
% 26.70/26.90      inference('demod', [status(thm)], ['366', '367', '368', '369'])).
% 26.70/26.90  thf('371', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_B)
% 26.70/26.90        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['370'])).
% 26.70/26.90  thf('372', plain,
% 26.70/26.90      (((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_B))),
% 26.70/26.90      inference('sup+', [status(thm)], ['355', '371'])).
% 26.70/26.90  thf('373', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_B)
% 26.70/26.90        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (k10_yellow_6 @ sk_A @ sk_B)))),
% 26.70/26.90      inference('simplify', [status(thm)], ['372'])).
% 26.70/26.90  thf('374', plain,
% 26.70/26.90      ((~ (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (k10_yellow_6 @ sk_A @ sk_B)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('split', [status(esa)], ['353'])).
% 26.70/26.90  thf('375', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_A)
% 26.70/26.90         | (r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 26.70/26.90         | (v2_struct_0 @ sk_B)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['373', '374'])).
% 26.70/26.90  thf('376', plain, (~ (v2_struct_0 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('377', plain,
% 26.70/26.90      ((((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 26.70/26.90         | (v2_struct_0 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('clc', [status(thm)], ['375', '376'])).
% 26.70/26.90  thf('378', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.90      inference('clc', [status(thm)], ['69', '70'])).
% 26.70/26.90  thf('379', plain,
% 26.70/26.90      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('clc', [status(thm)], ['11', '12'])).
% 26.70/26.90  thf('380', plain,
% 26.70/26.90      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('clc', [status(thm)], ['23', '24'])).
% 26.70/26.90  thf('381', plain,
% 26.70/26.90      (![X34 : $i, X35 : $i, X36 : $i]:
% 26.70/26.90         ((v2_struct_0 @ X34)
% 26.70/26.90          | ~ (v4_orders_2 @ X34)
% 26.70/26.90          | ~ (v7_waybel_0 @ X34)
% 26.70/26.90          | ~ (l1_waybel_0 @ X34 @ X35)
% 26.70/26.90          | ~ (r3_waybel_9 @ X35 @ X34 @ X36)
% 26.70/26.90          | (r2_hidden @ X36 @ (k10_yellow_6 @ X35 @ X34))
% 26.70/26.90          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 26.70/26.90          | (m1_subset_1 @ (sk_C_1 @ X34 @ X35) @ (u1_struct_0 @ X35))
% 26.70/26.90          | ~ (l1_pre_topc @ X35)
% 26.70/26.90          | ~ (v1_compts_1 @ X35)
% 26.70/26.90          | ~ (v8_pre_topc @ X35)
% 26.70/26.90          | ~ (v2_pre_topc @ X35)
% 26.70/26.90          | (v2_struct_0 @ X35))),
% 26.70/26.90      inference('cnf', [status(esa)], [t33_waybel_9])).
% 26.70/26.90  thf('382', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_A)
% 26.70/26.90          | ~ (v2_pre_topc @ sk_A)
% 26.70/26.90          | ~ (v8_pre_topc @ sk_A)
% 26.70/26.90          | ~ (v1_compts_1 @ sk_A)
% 26.70/26.90          | ~ (l1_pre_topc @ sk_A)
% 26.70/26.90          | (m1_subset_1 @ (sk_C_1 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 26.70/26.90          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90          | ~ (v7_waybel_0 @ X0)
% 26.70/26.90          | ~ (v4_orders_2 @ X0)
% 26.70/26.90          | (v2_struct_0 @ X0))),
% 26.70/26.90      inference('sup-', [status(thm)], ['380', '381'])).
% 26.70/26.90  thf('383', plain, ((v2_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('384', plain, ((v8_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('385', plain, ((v1_compts_1 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('386', plain, ((l1_pre_topc @ sk_A)),
% 26.70/26.90      inference('sup-', [status(thm)], ['6', '7'])).
% 26.70/26.90  thf('387', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_A)
% 26.70/26.90          | (m1_subset_1 @ (sk_C_1 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 26.70/26.90          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90          | ~ (v7_waybel_0 @ X0)
% 26.70/26.90          | ~ (v4_orders_2 @ X0)
% 26.70/26.90          | (v2_struct_0 @ X0))),
% 26.70/26.90      inference('demod', [status(thm)], ['382', '383', '384', '385', '386'])).
% 26.70/26.90  thf('388', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ X0)
% 26.70/26.90          | ~ (v4_orders_2 @ X0)
% 26.70/26.90          | ~ (v7_waybel_0 @ X0)
% 26.70/26.90          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 26.70/26.90          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 26.70/26.90          | (m1_subset_1 @ (sk_C_1 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90          | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['387'])).
% 26.70/26.90  thf('389', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 26.70/26.90        | ~ (v7_waybel_0 @ sk_B)
% 26.70/26.90        | ~ (v4_orders_2 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B))),
% 26.70/26.90      inference('sup-', [status(thm)], ['379', '388'])).
% 26.70/26.90  thf('390', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('391', plain, ((v7_waybel_0 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('392', plain, ((v4_orders_2 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('393', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90        | (v2_struct_0 @ sk_B))),
% 26.70/26.90      inference('demod', [status(thm)], ['389', '390', '391', '392'])).
% 26.70/26.90  thf('394', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_B)
% 26.70/26.90        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['393'])).
% 26.70/26.90  thf('395', plain,
% 26.70/26.90      (((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_B))),
% 26.70/26.90      inference('sup+', [status(thm)], ['378', '394'])).
% 26.70/26.90  thf('396', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_B)
% 26.70/26.90        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (k10_yellow_6 @ sk_A @ sk_B)))),
% 26.70/26.90      inference('simplify', [status(thm)], ['395'])).
% 26.70/26.90  thf('397', plain,
% 26.70/26.90      ((~ (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (k10_yellow_6 @ sk_A @ sk_B)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('split', [status(esa)], ['353'])).
% 26.70/26.90  thf('398', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_A)
% 26.70/26.90         | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90         | (v2_struct_0 @ sk_B)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['396', '397'])).
% 26.70/26.90  thf('399', plain, (~ (v2_struct_0 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('400', plain,
% 26.70/26.90      ((((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90         | (v2_struct_0 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('clc', [status(thm)], ['398', '399'])).
% 26.70/26.90  thf('401', plain,
% 26.70/26.90      ((((r3_waybel_9 @ sk_A @ sk_B @ (sk_C_1 @ sk_B @ sk_A))
% 26.70/26.90         | (v2_struct_0 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('clc', [status(thm)], ['375', '376'])).
% 26.70/26.90  thf('402', plain,
% 26.70/26.90      ((((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90         | (v2_struct_0 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('clc', [status(thm)], ['398', '399'])).
% 26.70/26.90  thf('403', plain,
% 26.70/26.90      (![X37 : $i, X38 : $i, X39 : $i]:
% 26.70/26.90         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 26.70/26.90          | (m1_subset_1 @ (sk_D_2 @ X38) @ (u1_struct_0 @ X38))
% 26.70/26.90          | ~ (v10_waybel_0 @ X39 @ X38)
% 26.70/26.90          | ~ (r3_waybel_9 @ X38 @ X39 @ X37)
% 26.70/26.90          | ((X37) = (k1_waybel_2 @ X38 @ X39))
% 26.70/26.90          | ~ (l1_waybel_0 @ X39 @ X38)
% 26.70/26.90          | ~ (v7_waybel_0 @ X39)
% 26.70/26.90          | ~ (v4_orders_2 @ X39)
% 26.70/26.90          | (v2_struct_0 @ X39)
% 26.70/26.90          | ~ (l1_waybel_9 @ X38)
% 26.70/26.90          | ~ (v1_compts_1 @ X38)
% 26.70/26.90          | ~ (v2_lattice3 @ X38)
% 26.70/26.90          | ~ (v1_lattice3 @ X38)
% 26.70/26.90          | ~ (v5_orders_2 @ X38)
% 26.70/26.90          | ~ (v4_orders_2 @ X38)
% 26.70/26.90          | ~ (v3_orders_2 @ X38)
% 26.70/26.90          | ~ (v8_pre_topc @ X38)
% 26.70/26.90          | ~ (v2_pre_topc @ X38))),
% 26.70/26.90      inference('cnf', [status(esa)], [t35_waybel_9])).
% 26.70/26.90  thf('404', plain,
% 26.70/26.90      ((![X0 : $i]:
% 26.70/26.90          ((v2_struct_0 @ sk_A)
% 26.70/26.90           | ~ (v2_pre_topc @ sk_A)
% 26.70/26.90           | ~ (v8_pre_topc @ sk_A)
% 26.70/26.90           | ~ (v3_orders_2 @ sk_A)
% 26.70/26.90           | ~ (v4_orders_2 @ sk_A)
% 26.70/26.90           | ~ (v5_orders_2 @ sk_A)
% 26.70/26.90           | ~ (v1_lattice3 @ sk_A)
% 26.70/26.90           | ~ (v2_lattice3 @ sk_A)
% 26.70/26.90           | ~ (v1_compts_1 @ sk_A)
% 26.70/26.90           | ~ (l1_waybel_9 @ sk_A)
% 26.70/26.90           | (v2_struct_0 @ X0)
% 26.70/26.90           | ~ (v4_orders_2 @ X0)
% 26.70/26.90           | ~ (v7_waybel_0 @ X0)
% 26.70/26.90           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 26.70/26.90           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 26.70/26.90           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['402', '403'])).
% 26.70/26.90  thf('405', plain, ((v2_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('406', plain, ((v8_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('407', plain, ((v3_orders_2 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('408', plain, ((v4_orders_2 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('409', plain, ((v5_orders_2 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('410', plain, ((v1_lattice3 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('411', plain, ((v2_lattice3 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('412', plain, ((v1_compts_1 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('413', plain, ((l1_waybel_9 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('414', plain,
% 26.70/26.90      ((![X0 : $i]:
% 26.70/26.90          ((v2_struct_0 @ sk_A)
% 26.70/26.90           | (v2_struct_0 @ X0)
% 26.70/26.90           | ~ (v4_orders_2 @ X0)
% 26.70/26.90           | ~ (v7_waybel_0 @ X0)
% 26.70/26.90           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 26.70/26.90           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 26.70/26.90           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('demod', [status(thm)],
% 26.70/26.90                ['404', '405', '406', '407', '408', '409', '410', '411', 
% 26.70/26.90                 '412', '413'])).
% 26.70/26.90  thf('415', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_A)
% 26.70/26.90         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90         | ~ (v10_waybel_0 @ sk_B @ sk_A)
% 26.70/26.90         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 26.70/26.90         | ~ (v7_waybel_0 @ sk_B)
% 26.70/26.90         | ~ (v4_orders_2 @ sk_B)
% 26.70/26.90         | (v2_struct_0 @ sk_B)
% 26.70/26.90         | (v2_struct_0 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['401', '414'])).
% 26.70/26.90  thf('416', plain, ((v10_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('417', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('418', plain, ((v7_waybel_0 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('419', plain, ((v4_orders_2 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('420', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_A)
% 26.70/26.90         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | (v2_struct_0 @ sk_B)
% 26.70/26.90         | (v2_struct_0 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('demod', [status(thm)], ['415', '416', '417', '418', '419'])).
% 26.70/26.90  thf('421', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_B)
% 26.70/26.90         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90         | (v2_struct_0 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('simplify', [status(thm)], ['420'])).
% 26.70/26.90  thf('422', plain,
% 26.70/26.90      (![X40 : $i]:
% 26.70/26.90         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X40) @ sk_A @ sk_A)
% 26.70/26.90          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ sk_A)))),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('423', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_A)
% 26.70/26.90         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | (v2_struct_0 @ sk_B)
% 26.70/26.90         | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_D_2 @ sk_A)) @ sk_A @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['421', '422'])).
% 26.70/26.90  thf('424', plain,
% 26.70/26.90      (![X37 : $i, X38 : $i, X39 : $i]:
% 26.70/26.90         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 26.70/26.90          | ~ (v5_pre_topc @ (k4_waybel_1 @ X38 @ (sk_D_2 @ X38)) @ X38 @ X38)
% 26.70/26.90          | ~ (v10_waybel_0 @ X39 @ X38)
% 26.70/26.90          | ~ (r3_waybel_9 @ X38 @ X39 @ X37)
% 26.70/26.90          | ((X37) = (k1_waybel_2 @ X38 @ X39))
% 26.70/26.90          | ~ (l1_waybel_0 @ X39 @ X38)
% 26.70/26.90          | ~ (v7_waybel_0 @ X39)
% 26.70/26.90          | ~ (v4_orders_2 @ X39)
% 26.70/26.90          | (v2_struct_0 @ X39)
% 26.70/26.90          | ~ (l1_waybel_9 @ X38)
% 26.70/26.90          | ~ (v1_compts_1 @ X38)
% 26.70/26.90          | ~ (v2_lattice3 @ X38)
% 26.70/26.90          | ~ (v1_lattice3 @ X38)
% 26.70/26.90          | ~ (v5_orders_2 @ X38)
% 26.70/26.90          | ~ (v4_orders_2 @ X38)
% 26.70/26.90          | ~ (v3_orders_2 @ X38)
% 26.70/26.90          | ~ (v8_pre_topc @ X38)
% 26.70/26.90          | ~ (v2_pre_topc @ X38))),
% 26.70/26.90      inference('cnf', [status(esa)], [t35_waybel_9])).
% 26.70/26.90  thf('425', plain,
% 26.70/26.90      ((![X0 : $i, X1 : $i]:
% 26.70/26.90          ((v2_struct_0 @ sk_B)
% 26.70/26.90           | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90           | (v2_struct_0 @ sk_A)
% 26.70/26.90           | ~ (v2_pre_topc @ sk_A)
% 26.70/26.90           | ~ (v8_pre_topc @ sk_A)
% 26.70/26.90           | ~ (v3_orders_2 @ sk_A)
% 26.70/26.90           | ~ (v4_orders_2 @ sk_A)
% 26.70/26.90           | ~ (v5_orders_2 @ sk_A)
% 26.70/26.90           | ~ (v1_lattice3 @ sk_A)
% 26.70/26.90           | ~ (v2_lattice3 @ sk_A)
% 26.70/26.90           | ~ (v1_compts_1 @ sk_A)
% 26.70/26.90           | ~ (l1_waybel_9 @ sk_A)
% 26.70/26.90           | (v2_struct_0 @ X0)
% 26.70/26.90           | ~ (v4_orders_2 @ X0)
% 26.70/26.90           | ~ (v7_waybel_0 @ X0)
% 26.70/26.90           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | ((X1) = (k1_waybel_2 @ sk_A @ X0))
% 26.70/26.90           | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 26.70/26.90           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['423', '424'])).
% 26.70/26.90  thf('426', plain, ((v2_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('427', plain, ((v8_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('428', plain, ((v3_orders_2 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('429', plain, ((v4_orders_2 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('430', plain, ((v5_orders_2 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('431', plain, ((v1_lattice3 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('432', plain, ((v2_lattice3 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('433', plain, ((v1_compts_1 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('434', plain, ((l1_waybel_9 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('435', plain,
% 26.70/26.90      ((![X0 : $i, X1 : $i]:
% 26.70/26.90          ((v2_struct_0 @ sk_B)
% 26.70/26.90           | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90           | (v2_struct_0 @ sk_A)
% 26.70/26.90           | (v2_struct_0 @ X0)
% 26.70/26.90           | ~ (v4_orders_2 @ X0)
% 26.70/26.90           | ~ (v7_waybel_0 @ X0)
% 26.70/26.90           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | ((X1) = (k1_waybel_2 @ sk_A @ X0))
% 26.70/26.90           | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 26.70/26.90           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('demod', [status(thm)],
% 26.70/26.90                ['425', '426', '427', '428', '429', '430', '431', '432', 
% 26.70/26.90                 '433', '434'])).
% 26.70/26.90  thf('436', plain,
% 26.70/26.90      ((![X0 : $i]:
% 26.70/26.90          ((v2_struct_0 @ sk_A)
% 26.70/26.90           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 26.70/26.90           | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 26.70/26.90           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | ~ (v7_waybel_0 @ X0)
% 26.70/26.90           | ~ (v4_orders_2 @ X0)
% 26.70/26.90           | (v2_struct_0 @ X0)
% 26.70/26.90           | (v2_struct_0 @ sk_A)
% 26.70/26.90           | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90           | (v2_struct_0 @ sk_B)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['400', '435'])).
% 26.70/26.90  thf('437', plain,
% 26.70/26.90      ((![X0 : $i]:
% 26.70/26.90          ((v2_struct_0 @ sk_B)
% 26.70/26.90           | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90           | (v2_struct_0 @ X0)
% 26.70/26.90           | ~ (v4_orders_2 @ X0)
% 26.70/26.90           | ~ (v7_waybel_0 @ X0)
% 26.70/26.90           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 26.70/26.90           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 26.70/26.90           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | (v2_struct_0 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('simplify', [status(thm)], ['436'])).
% 26.70/26.90  thf('438', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_A)
% 26.70/26.90         | (v2_struct_0 @ sk_A)
% 26.70/26.90         | ~ (v10_waybel_0 @ sk_B @ sk_A)
% 26.70/26.90         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 26.70/26.90         | ~ (v7_waybel_0 @ sk_B)
% 26.70/26.90         | ~ (v4_orders_2 @ sk_B)
% 26.70/26.90         | (v2_struct_0 @ sk_B)
% 26.70/26.90         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | (v2_struct_0 @ sk_B)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['377', '437'])).
% 26.70/26.90  thf('439', plain, ((v10_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('440', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('441', plain, ((v7_waybel_0 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('442', plain, ((v4_orders_2 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('443', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_A)
% 26.70/26.90         | (v2_struct_0 @ sk_A)
% 26.70/26.90         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | (v2_struct_0 @ sk_B)
% 26.70/26.90         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | (v2_struct_0 @ sk_B)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('demod', [status(thm)], ['438', '439', '440', '441', '442'])).
% 26.70/26.90  thf('444', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_B)
% 26.70/26.90         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | (v2_struct_0 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('simplify', [status(thm)], ['443'])).
% 26.70/26.90  thf('445', plain, (~ (v2_struct_0 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('446', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_A)
% 26.70/26.90         | ((sk_C_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('clc', [status(thm)], ['444', '445'])).
% 26.70/26.90  thf('447', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.90      inference('clc', [status(thm)], ['69', '70'])).
% 26.70/26.90  thf('448', plain,
% 26.70/26.90      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('clc', [status(thm)], ['11', '12'])).
% 26.70/26.90  thf('449', plain,
% 26.70/26.90      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('clc', [status(thm)], ['23', '24'])).
% 26.70/26.90  thf('450', plain,
% 26.70/26.90      (![X34 : $i, X35 : $i, X36 : $i]:
% 26.70/26.90         ((v2_struct_0 @ X34)
% 26.70/26.90          | ~ (v4_orders_2 @ X34)
% 26.70/26.90          | ~ (v7_waybel_0 @ X34)
% 26.70/26.90          | ~ (l1_waybel_0 @ X34 @ X35)
% 26.70/26.90          | ~ (r3_waybel_9 @ X35 @ X34 @ X36)
% 26.70/26.90          | (r2_hidden @ X36 @ (k10_yellow_6 @ X35 @ X34))
% 26.70/26.90          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 26.70/26.90          | (r3_waybel_9 @ X35 @ X34 @ (sk_D_1 @ X34 @ X35))
% 26.70/26.90          | ~ (l1_pre_topc @ X35)
% 26.70/26.90          | ~ (v1_compts_1 @ X35)
% 26.70/26.90          | ~ (v8_pre_topc @ X35)
% 26.70/26.90          | ~ (v2_pre_topc @ X35)
% 26.70/26.90          | (v2_struct_0 @ X35))),
% 26.70/26.90      inference('cnf', [status(esa)], [t33_waybel_9])).
% 26.70/26.90  thf('451', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_A)
% 26.70/26.90          | ~ (v2_pre_topc @ sk_A)
% 26.70/26.90          | ~ (v8_pre_topc @ sk_A)
% 26.70/26.90          | ~ (v1_compts_1 @ sk_A)
% 26.70/26.90          | ~ (l1_pre_topc @ sk_A)
% 26.70/26.90          | (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ X0 @ sk_A))
% 26.70/26.90          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 26.70/26.90          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90          | ~ (v7_waybel_0 @ X0)
% 26.70/26.90          | ~ (v4_orders_2 @ X0)
% 26.70/26.90          | (v2_struct_0 @ X0))),
% 26.70/26.90      inference('sup-', [status(thm)], ['449', '450'])).
% 26.70/26.90  thf('452', plain, ((v2_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('453', plain, ((v8_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('454', plain, ((v1_compts_1 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('455', plain, ((l1_pre_topc @ sk_A)),
% 26.70/26.90      inference('sup-', [status(thm)], ['6', '7'])).
% 26.70/26.90  thf('456', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_A)
% 26.70/26.90          | (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ X0 @ sk_A))
% 26.70/26.90          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 26.70/26.90          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90          | ~ (v7_waybel_0 @ X0)
% 26.70/26.90          | ~ (v4_orders_2 @ X0)
% 26.70/26.90          | (v2_struct_0 @ X0))),
% 26.70/26.90      inference('demod', [status(thm)], ['451', '452', '453', '454', '455'])).
% 26.70/26.90  thf('457', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ X0)
% 26.70/26.90          | ~ (v4_orders_2 @ X0)
% 26.70/26.90          | ~ (v7_waybel_0 @ X0)
% 26.70/26.90          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 26.70/26.90          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 26.70/26.90          | (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ X0 @ sk_A))
% 26.70/26.90          | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['456'])).
% 26.70/26.90  thf('458', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 26.70/26.90        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 26.70/26.90        | ~ (v7_waybel_0 @ sk_B)
% 26.70/26.90        | ~ (v4_orders_2 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B))),
% 26.70/26.90      inference('sup-', [status(thm)], ['448', '457'])).
% 26.70/26.90  thf('459', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('460', plain, ((v7_waybel_0 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('461', plain, ((v4_orders_2 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('462', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 26.70/26.90        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90        | (v2_struct_0 @ sk_B))),
% 26.70/26.90      inference('demod', [status(thm)], ['458', '459', '460', '461'])).
% 26.70/26.90  thf('463', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_B)
% 26.70/26.90        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['462'])).
% 26.70/26.90  thf('464', plain,
% 26.70/26.90      (((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_B))),
% 26.70/26.90      inference('sup+', [status(thm)], ['447', '463'])).
% 26.70/26.90  thf('465', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_B)
% 26.70/26.90        | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (k10_yellow_6 @ sk_A @ sk_B)))),
% 26.70/26.90      inference('simplify', [status(thm)], ['464'])).
% 26.70/26.90  thf('466', plain,
% 26.70/26.90      ((~ (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (k10_yellow_6 @ sk_A @ sk_B)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('split', [status(esa)], ['353'])).
% 26.70/26.90  thf('467', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_A)
% 26.70/26.90         | (r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 26.70/26.90         | (v2_struct_0 @ sk_B)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['465', '466'])).
% 26.70/26.90  thf('468', plain, (~ (v2_struct_0 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('469', plain,
% 26.70/26.90      ((((r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 26.70/26.90         | (v2_struct_0 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('clc', [status(thm)], ['467', '468'])).
% 26.70/26.90  thf('470', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | ((sk_C @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.90      inference('clc', [status(thm)], ['69', '70'])).
% 26.70/26.90  thf('471', plain,
% 26.70/26.90      (((r3_waybel_9 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('clc', [status(thm)], ['11', '12'])).
% 26.70/26.90  thf('472', plain,
% 26.70/26.90      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('clc', [status(thm)], ['23', '24'])).
% 26.70/26.90  thf('473', plain,
% 26.70/26.90      (![X34 : $i, X35 : $i, X36 : $i]:
% 26.70/26.90         ((v2_struct_0 @ X34)
% 26.70/26.90          | ~ (v4_orders_2 @ X34)
% 26.70/26.90          | ~ (v7_waybel_0 @ X34)
% 26.70/26.90          | ~ (l1_waybel_0 @ X34 @ X35)
% 26.70/26.90          | ~ (r3_waybel_9 @ X35 @ X34 @ X36)
% 26.70/26.90          | (r2_hidden @ X36 @ (k10_yellow_6 @ X35 @ X34))
% 26.70/26.90          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 26.70/26.90          | (m1_subset_1 @ (sk_D_1 @ X34 @ X35) @ (u1_struct_0 @ X35))
% 26.70/26.90          | ~ (l1_pre_topc @ X35)
% 26.70/26.90          | ~ (v1_compts_1 @ X35)
% 26.70/26.90          | ~ (v8_pre_topc @ X35)
% 26.70/26.90          | ~ (v2_pre_topc @ X35)
% 26.70/26.90          | (v2_struct_0 @ X35))),
% 26.70/26.90      inference('cnf', [status(esa)], [t33_waybel_9])).
% 26.70/26.90  thf('474', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_A)
% 26.70/26.90          | ~ (v2_pre_topc @ sk_A)
% 26.70/26.90          | ~ (v8_pre_topc @ sk_A)
% 26.70/26.90          | ~ (v1_compts_1 @ sk_A)
% 26.70/26.90          | ~ (l1_pre_topc @ sk_A)
% 26.70/26.90          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 26.70/26.90          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90          | ~ (v7_waybel_0 @ X0)
% 26.70/26.90          | ~ (v4_orders_2 @ X0)
% 26.70/26.90          | (v2_struct_0 @ X0))),
% 26.70/26.90      inference('sup-', [status(thm)], ['472', '473'])).
% 26.70/26.90  thf('475', plain, ((v2_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('476', plain, ((v8_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('477', plain, ((v1_compts_1 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('478', plain, ((l1_pre_topc @ sk_A)),
% 26.70/26.90      inference('sup-', [status(thm)], ['6', '7'])).
% 26.70/26.90  thf('479', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_A)
% 26.70/26.90          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 26.70/26.90          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90          | ~ (v7_waybel_0 @ X0)
% 26.70/26.90          | ~ (v4_orders_2 @ X0)
% 26.70/26.90          | (v2_struct_0 @ X0))),
% 26.70/26.90      inference('demod', [status(thm)], ['474', '475', '476', '477', '478'])).
% 26.70/26.90  thf('480', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ X0)
% 26.70/26.90          | ~ (v4_orders_2 @ X0)
% 26.70/26.90          | ~ (v7_waybel_0 @ X0)
% 26.70/26.90          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B @ sk_A))
% 26.70/26.90          | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ X0))
% 26.70/26.90          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90          | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['479'])).
% 26.70/26.90  thf('481', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 26.70/26.90        | ~ (v7_waybel_0 @ sk_B)
% 26.70/26.90        | ~ (v4_orders_2 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B))),
% 26.70/26.90      inference('sup-', [status(thm)], ['471', '480'])).
% 26.70/26.90  thf('482', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('483', plain, ((v7_waybel_0 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('484', plain, ((v4_orders_2 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('485', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90        | (v2_struct_0 @ sk_B))),
% 26.70/26.90      inference('demod', [status(thm)], ['481', '482', '483', '484'])).
% 26.70/26.90  thf('486', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_B)
% 26.70/26.90        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['485'])).
% 26.70/26.90  thf('487', plain,
% 26.70/26.90      (((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_B))),
% 26.70/26.90      inference('sup+', [status(thm)], ['470', '486'])).
% 26.70/26.90  thf('488', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_B)
% 26.70/26.90        | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (k10_yellow_6 @ sk_A @ sk_B)))),
% 26.70/26.90      inference('simplify', [status(thm)], ['487'])).
% 26.70/26.90  thf('489', plain,
% 26.70/26.90      ((~ (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (k10_yellow_6 @ sk_A @ sk_B)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('split', [status(esa)], ['353'])).
% 26.70/26.90  thf('490', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_A)
% 26.70/26.90         | (m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90         | (v2_struct_0 @ sk_B)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['488', '489'])).
% 26.70/26.90  thf('491', plain, (~ (v2_struct_0 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('492', plain,
% 26.70/26.90      ((((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90         | (v2_struct_0 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('clc', [status(thm)], ['490', '491'])).
% 26.70/26.90  thf('493', plain,
% 26.70/26.90      ((((r3_waybel_9 @ sk_A @ sk_B @ (sk_D_1 @ sk_B @ sk_A))
% 26.70/26.90         | (v2_struct_0 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('clc', [status(thm)], ['467', '468'])).
% 26.70/26.90  thf('494', plain,
% 26.70/26.90      ((((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90         | (v2_struct_0 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('clc', [status(thm)], ['490', '491'])).
% 26.70/26.90  thf('495', plain,
% 26.70/26.90      (![X37 : $i, X38 : $i, X39 : $i]:
% 26.70/26.90         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 26.70/26.90          | (m1_subset_1 @ (sk_D_2 @ X38) @ (u1_struct_0 @ X38))
% 26.70/26.90          | ~ (v10_waybel_0 @ X39 @ X38)
% 26.70/26.90          | ~ (r3_waybel_9 @ X38 @ X39 @ X37)
% 26.70/26.90          | ((X37) = (k1_waybel_2 @ X38 @ X39))
% 26.70/26.90          | ~ (l1_waybel_0 @ X39 @ X38)
% 26.70/26.90          | ~ (v7_waybel_0 @ X39)
% 26.70/26.90          | ~ (v4_orders_2 @ X39)
% 26.70/26.90          | (v2_struct_0 @ X39)
% 26.70/26.90          | ~ (l1_waybel_9 @ X38)
% 26.70/26.90          | ~ (v1_compts_1 @ X38)
% 26.70/26.90          | ~ (v2_lattice3 @ X38)
% 26.70/26.90          | ~ (v1_lattice3 @ X38)
% 26.70/26.90          | ~ (v5_orders_2 @ X38)
% 26.70/26.90          | ~ (v4_orders_2 @ X38)
% 26.70/26.90          | ~ (v3_orders_2 @ X38)
% 26.70/26.90          | ~ (v8_pre_topc @ X38)
% 26.70/26.90          | ~ (v2_pre_topc @ X38))),
% 26.70/26.90      inference('cnf', [status(esa)], [t35_waybel_9])).
% 26.70/26.90  thf('496', plain,
% 26.70/26.90      ((![X0 : $i]:
% 26.70/26.90          ((v2_struct_0 @ sk_A)
% 26.70/26.90           | ~ (v2_pre_topc @ sk_A)
% 26.70/26.90           | ~ (v8_pre_topc @ sk_A)
% 26.70/26.90           | ~ (v3_orders_2 @ sk_A)
% 26.70/26.90           | ~ (v4_orders_2 @ sk_A)
% 26.70/26.90           | ~ (v5_orders_2 @ sk_A)
% 26.70/26.90           | ~ (v1_lattice3 @ sk_A)
% 26.70/26.90           | ~ (v2_lattice3 @ sk_A)
% 26.70/26.90           | ~ (v1_compts_1 @ sk_A)
% 26.70/26.90           | ~ (l1_waybel_9 @ sk_A)
% 26.70/26.90           | (v2_struct_0 @ X0)
% 26.70/26.90           | ~ (v4_orders_2 @ X0)
% 26.70/26.90           | ~ (v7_waybel_0 @ X0)
% 26.70/26.90           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 26.70/26.90           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_A))
% 26.70/26.90           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['494', '495'])).
% 26.70/26.90  thf('497', plain, ((v2_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('498', plain, ((v8_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('499', plain, ((v3_orders_2 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('500', plain, ((v4_orders_2 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('501', plain, ((v5_orders_2 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('502', plain, ((v1_lattice3 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('503', plain, ((v2_lattice3 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('504', plain, ((v1_compts_1 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('505', plain, ((l1_waybel_9 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('506', plain,
% 26.70/26.90      ((![X0 : $i]:
% 26.70/26.90          ((v2_struct_0 @ sk_A)
% 26.70/26.90           | (v2_struct_0 @ X0)
% 26.70/26.90           | ~ (v4_orders_2 @ X0)
% 26.70/26.90           | ~ (v7_waybel_0 @ X0)
% 26.70/26.90           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 26.70/26.90           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_A))
% 26.70/26.90           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('demod', [status(thm)],
% 26.70/26.90                ['496', '497', '498', '499', '500', '501', '502', '503', 
% 26.70/26.90                 '504', '505'])).
% 26.70/26.90  thf('507', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_A)
% 26.70/26.90         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90         | ~ (v10_waybel_0 @ sk_B @ sk_A)
% 26.70/26.90         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 26.70/26.90         | ~ (v7_waybel_0 @ sk_B)
% 26.70/26.90         | ~ (v4_orders_2 @ sk_B)
% 26.70/26.90         | (v2_struct_0 @ sk_B)
% 26.70/26.90         | (v2_struct_0 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['493', '506'])).
% 26.70/26.90  thf('508', plain, ((v10_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('509', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('510', plain, ((v7_waybel_0 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('511', plain, ((v4_orders_2 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('512', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_A)
% 26.70/26.90         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | (v2_struct_0 @ sk_B)
% 26.70/26.90         | (v2_struct_0 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('demod', [status(thm)], ['507', '508', '509', '510', '511'])).
% 26.70/26.90  thf('513', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_B)
% 26.70/26.90         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | (m1_subset_1 @ (sk_D_2 @ sk_A) @ (u1_struct_0 @ sk_A))
% 26.70/26.90         | (v2_struct_0 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('simplify', [status(thm)], ['512'])).
% 26.70/26.90  thf('514', plain,
% 26.70/26.90      (![X40 : $i]:
% 26.70/26.90         ((v5_pre_topc @ (k4_waybel_1 @ sk_A @ X40) @ sk_A @ sk_A)
% 26.70/26.90          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ sk_A)))),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('515', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_A)
% 26.70/26.90         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | (v2_struct_0 @ sk_B)
% 26.70/26.90         | (v5_pre_topc @ (k4_waybel_1 @ sk_A @ (sk_D_2 @ sk_A)) @ sk_A @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['513', '514'])).
% 26.70/26.90  thf('516', plain,
% 26.70/26.90      (![X37 : $i, X38 : $i, X39 : $i]:
% 26.70/26.90         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 26.70/26.90          | ~ (v5_pre_topc @ (k4_waybel_1 @ X38 @ (sk_D_2 @ X38)) @ X38 @ X38)
% 26.70/26.90          | ~ (v10_waybel_0 @ X39 @ X38)
% 26.70/26.90          | ~ (r3_waybel_9 @ X38 @ X39 @ X37)
% 26.70/26.90          | ((X37) = (k1_waybel_2 @ X38 @ X39))
% 26.70/26.90          | ~ (l1_waybel_0 @ X39 @ X38)
% 26.70/26.90          | ~ (v7_waybel_0 @ X39)
% 26.70/26.90          | ~ (v4_orders_2 @ X39)
% 26.70/26.90          | (v2_struct_0 @ X39)
% 26.70/26.90          | ~ (l1_waybel_9 @ X38)
% 26.70/26.90          | ~ (v1_compts_1 @ X38)
% 26.70/26.90          | ~ (v2_lattice3 @ X38)
% 26.70/26.90          | ~ (v1_lattice3 @ X38)
% 26.70/26.90          | ~ (v5_orders_2 @ X38)
% 26.70/26.90          | ~ (v4_orders_2 @ X38)
% 26.70/26.90          | ~ (v3_orders_2 @ X38)
% 26.70/26.90          | ~ (v8_pre_topc @ X38)
% 26.70/26.90          | ~ (v2_pre_topc @ X38))),
% 26.70/26.90      inference('cnf', [status(esa)], [t35_waybel_9])).
% 26.70/26.90  thf('517', plain,
% 26.70/26.90      ((![X0 : $i, X1 : $i]:
% 26.70/26.90          ((v2_struct_0 @ sk_B)
% 26.70/26.90           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90           | (v2_struct_0 @ sk_A)
% 26.70/26.90           | ~ (v2_pre_topc @ sk_A)
% 26.70/26.90           | ~ (v8_pre_topc @ sk_A)
% 26.70/26.90           | ~ (v3_orders_2 @ sk_A)
% 26.70/26.90           | ~ (v4_orders_2 @ sk_A)
% 26.70/26.90           | ~ (v5_orders_2 @ sk_A)
% 26.70/26.90           | ~ (v1_lattice3 @ sk_A)
% 26.70/26.90           | ~ (v2_lattice3 @ sk_A)
% 26.70/26.90           | ~ (v1_compts_1 @ sk_A)
% 26.70/26.90           | ~ (l1_waybel_9 @ sk_A)
% 26.70/26.90           | (v2_struct_0 @ X0)
% 26.70/26.90           | ~ (v4_orders_2 @ X0)
% 26.70/26.90           | ~ (v7_waybel_0 @ X0)
% 26.70/26.90           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | ((X1) = (k1_waybel_2 @ sk_A @ X0))
% 26.70/26.90           | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 26.70/26.90           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['515', '516'])).
% 26.70/26.90  thf('518', plain, ((v2_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('519', plain, ((v8_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('520', plain, ((v3_orders_2 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('521', plain, ((v4_orders_2 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('522', plain, ((v5_orders_2 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('523', plain, ((v1_lattice3 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('524', plain, ((v2_lattice3 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('525', plain, ((v1_compts_1 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('526', plain, ((l1_waybel_9 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('527', plain,
% 26.70/26.90      ((![X0 : $i, X1 : $i]:
% 26.70/26.90          ((v2_struct_0 @ sk_B)
% 26.70/26.90           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90           | (v2_struct_0 @ sk_A)
% 26.70/26.90           | (v2_struct_0 @ X0)
% 26.70/26.90           | ~ (v4_orders_2 @ X0)
% 26.70/26.90           | ~ (v7_waybel_0 @ X0)
% 26.70/26.90           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | ((X1) = (k1_waybel_2 @ sk_A @ X0))
% 26.70/26.90           | ~ (r3_waybel_9 @ sk_A @ X0 @ X1)
% 26.70/26.90           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('demod', [status(thm)],
% 26.70/26.90                ['517', '518', '519', '520', '521', '522', '523', '524', 
% 26.70/26.90                 '525', '526'])).
% 26.70/26.90  thf('528', plain,
% 26.70/26.90      ((![X0 : $i]:
% 26.70/26.90          ((v2_struct_0 @ sk_A)
% 26.70/26.90           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_A))
% 26.70/26.90           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 26.70/26.90           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | ~ (v7_waybel_0 @ X0)
% 26.70/26.90           | ~ (v4_orders_2 @ X0)
% 26.70/26.90           | (v2_struct_0 @ X0)
% 26.70/26.90           | (v2_struct_0 @ sk_A)
% 26.70/26.90           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90           | (v2_struct_0 @ sk_B)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['492', '527'])).
% 26.70/26.90  thf('529', plain,
% 26.70/26.90      ((![X0 : $i]:
% 26.70/26.90          ((v2_struct_0 @ sk_B)
% 26.70/26.90           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90           | (v2_struct_0 @ X0)
% 26.70/26.90           | ~ (v4_orders_2 @ X0)
% 26.70/26.90           | ~ (v7_waybel_0 @ X0)
% 26.70/26.90           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ X0))
% 26.70/26.90           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_D_1 @ sk_B @ sk_A))
% 26.70/26.90           | ~ (v10_waybel_0 @ X0 @ sk_A)
% 26.70/26.90           | (v2_struct_0 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('simplify', [status(thm)], ['528'])).
% 26.70/26.90  thf('530', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_A)
% 26.70/26.90         | (v2_struct_0 @ sk_A)
% 26.70/26.90         | ~ (v10_waybel_0 @ sk_B @ sk_A)
% 26.70/26.90         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 26.70/26.90         | ~ (v7_waybel_0 @ sk_B)
% 26.70/26.90         | ~ (v4_orders_2 @ sk_B)
% 26.70/26.90         | (v2_struct_0 @ sk_B)
% 26.70/26.90         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | (v2_struct_0 @ sk_B)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['469', '529'])).
% 26.70/26.90  thf('531', plain, ((v10_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('532', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('533', plain, ((v7_waybel_0 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('534', plain, ((v4_orders_2 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('535', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_A)
% 26.70/26.90         | (v2_struct_0 @ sk_A)
% 26.70/26.90         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | (v2_struct_0 @ sk_B)
% 26.70/26.90         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | (v2_struct_0 @ sk_B)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('demod', [status(thm)], ['530', '531', '532', '533', '534'])).
% 26.70/26.90  thf('536', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_B)
% 26.70/26.90         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | (v2_struct_0 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('simplify', [status(thm)], ['535'])).
% 26.70/26.90  thf('537', plain, (~ (v2_struct_0 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('538', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_A)
% 26.70/26.90         | ((sk_D_1 @ sk_B @ sk_A) = (k1_waybel_2 @ sk_A @ sk_B))))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('clc', [status(thm)], ['536', '537'])).
% 26.70/26.90  thf('539', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (r3_waybel_9 @ sk_A @ sk_B @ (k1_waybel_2 @ sk_A @ sk_B)))),
% 26.70/26.90      inference('simplify', [status(thm)], ['73'])).
% 26.70/26.90  thf('540', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (m1_subset_1 @ (k1_waybel_2 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 26.70/26.90      inference('simplify', [status(thm)], ['77'])).
% 26.70/26.90  thf('541', plain,
% 26.70/26.90      (![X34 : $i, X35 : $i, X36 : $i]:
% 26.70/26.90         ((v2_struct_0 @ X34)
% 26.70/26.90          | ~ (v4_orders_2 @ X34)
% 26.70/26.90          | ~ (v7_waybel_0 @ X34)
% 26.70/26.90          | ~ (l1_waybel_0 @ X34 @ X35)
% 26.70/26.90          | ~ (r3_waybel_9 @ X35 @ X34 @ X36)
% 26.70/26.90          | (r2_hidden @ X36 @ (k10_yellow_6 @ X35 @ X34))
% 26.70/26.90          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 26.70/26.90          | ((sk_C_1 @ X34 @ X35) != (sk_D_1 @ X34 @ X35))
% 26.70/26.90          | ~ (l1_pre_topc @ X35)
% 26.70/26.90          | ~ (v1_compts_1 @ X35)
% 26.70/26.90          | ~ (v8_pre_topc @ X35)
% 26.70/26.90          | ~ (v2_pre_topc @ X35)
% 26.70/26.90          | (v2_struct_0 @ X35))),
% 26.70/26.90      inference('cnf', [status(esa)], [t33_waybel_9])).
% 26.70/26.90  thf('542', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_A)
% 26.70/26.90          | ~ (v2_pre_topc @ sk_A)
% 26.70/26.90          | ~ (v8_pre_topc @ sk_A)
% 26.70/26.90          | ~ (v1_compts_1 @ sk_A)
% 26.70/26.90          | ~ (l1_pre_topc @ sk_A)
% 26.70/26.90          | ((sk_C_1 @ X0 @ sk_A) != (sk_D_1 @ X0 @ sk_A))
% 26.70/26.90          | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90             (k10_yellow_6 @ sk_A @ X0))
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90          | ~ (v7_waybel_0 @ X0)
% 26.70/26.90          | ~ (v4_orders_2 @ X0)
% 26.70/26.90          | (v2_struct_0 @ X0))),
% 26.70/26.90      inference('sup-', [status(thm)], ['540', '541'])).
% 26.70/26.90  thf('543', plain, ((v2_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('544', plain, ((v8_pre_topc @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('545', plain, ((v1_compts_1 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('546', plain, ((l1_pre_topc @ sk_A)),
% 26.70/26.90      inference('sup-', [status(thm)], ['6', '7'])).
% 26.70/26.90  thf('547', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ sk_A)
% 26.70/26.90          | (v2_struct_0 @ sk_A)
% 26.70/26.90          | ((sk_C_1 @ X0 @ sk_A) != (sk_D_1 @ X0 @ sk_A))
% 26.70/26.90          | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90             (k10_yellow_6 @ sk_A @ X0))
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90          | ~ (v7_waybel_0 @ X0)
% 26.70/26.90          | ~ (v4_orders_2 @ X0)
% 26.70/26.90          | (v2_struct_0 @ X0))),
% 26.70/26.90      inference('demod', [status(thm)], ['542', '543', '544', '545', '546'])).
% 26.70/26.90  thf('548', plain,
% 26.70/26.90      (![X0 : $i]:
% 26.70/26.90         ((v2_struct_0 @ X0)
% 26.70/26.90          | ~ (v4_orders_2 @ X0)
% 26.70/26.90          | ~ (v7_waybel_0 @ X0)
% 26.70/26.90          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 26.70/26.90          | ~ (r3_waybel_9 @ sk_A @ X0 @ (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90          | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90             (k10_yellow_6 @ sk_A @ X0))
% 26.70/26.90          | ((sk_C_1 @ X0 @ sk_A) != (sk_D_1 @ X0 @ sk_A))
% 26.70/26.90          | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['547'])).
% 26.70/26.90  thf('549', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | ((sk_C_1 @ sk_B @ sk_A) != (sk_D_1 @ sk_B @ sk_A))
% 26.70/26.90        | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 26.70/26.90        | ~ (v7_waybel_0 @ sk_B)
% 26.70/26.90        | ~ (v4_orders_2 @ sk_B)
% 26.70/26.90        | (v2_struct_0 @ sk_B))),
% 26.70/26.90      inference('sup-', [status(thm)], ['539', '548'])).
% 26.70/26.90  thf('550', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('551', plain, ((v7_waybel_0 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('552', plain, ((v4_orders_2 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('553', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A)
% 26.70/26.90        | (v2_struct_0 @ sk_A)
% 26.70/26.90        | ((sk_C_1 @ sk_B @ sk_A) != (sk_D_1 @ sk_B @ sk_A))
% 26.70/26.90        | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90        | (v2_struct_0 @ sk_B))),
% 26.70/26.90      inference('demod', [status(thm)], ['549', '550', '551', '552'])).
% 26.70/26.90  thf('554', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_B)
% 26.70/26.90        | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90        | ((sk_C_1 @ sk_B @ sk_A) != (sk_D_1 @ sk_B @ sk_A))
% 26.70/26.90        | (v2_struct_0 @ sk_A))),
% 26.70/26.90      inference('simplify', [status(thm)], ['553'])).
% 26.70/26.90  thf('555', plain,
% 26.70/26.90      (((((sk_C_1 @ sk_B @ sk_A) != (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | (v2_struct_0 @ sk_A)
% 26.70/26.90         | (v2_struct_0 @ sk_A)
% 26.70/26.90         | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90            (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90         | (v2_struct_0 @ sk_B)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['538', '554'])).
% 26.70/26.90  thf('556', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_B)
% 26.70/26.90         | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90            (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90         | (v2_struct_0 @ sk_A)
% 26.70/26.90         | ((sk_C_1 @ sk_B @ sk_A) != (k1_waybel_2 @ sk_A @ sk_B))))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('simplify', [status(thm)], ['555'])).
% 26.70/26.90  thf('557', plain,
% 26.70/26.90      (((((k1_waybel_2 @ sk_A @ sk_B) != (k1_waybel_2 @ sk_A @ sk_B))
% 26.70/26.90         | (v2_struct_0 @ sk_A)
% 26.70/26.90         | (v2_struct_0 @ sk_A)
% 26.70/26.90         | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90            (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90         | (v2_struct_0 @ sk_B)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['446', '556'])).
% 26.70/26.90  thf('558', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_B)
% 26.70/26.90         | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90            (k10_yellow_6 @ sk_A @ sk_B))
% 26.70/26.90         | (v2_struct_0 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('simplify', [status(thm)], ['557'])).
% 26.70/26.90  thf('559', plain, (~ (v2_struct_0 @ sk_B)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('560', plain,
% 26.70/26.90      ((((v2_struct_0 @ sk_A)
% 26.70/26.90         | (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90            (k10_yellow_6 @ sk_A @ sk_B))))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('clc', [status(thm)], ['558', '559'])).
% 26.70/26.90  thf('561', plain,
% 26.70/26.90      ((~ (r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90           (k10_yellow_6 @ sk_A @ sk_B)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('split', [status(esa)], ['353'])).
% 26.70/26.90  thf('562', plain,
% 26.70/26.90      (((v2_struct_0 @ sk_A))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('clc', [status(thm)], ['560', '561'])).
% 26.70/26.90  thf(cc1_lattice3, axiom,
% 26.70/26.90    (![A:$i]:
% 26.70/26.90     ( ( l1_orders_2 @ A ) =>
% 26.70/26.90       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 26.70/26.90  thf('563', plain,
% 26.70/26.90      (![X3 : $i]:
% 26.70/26.90         (~ (v1_lattice3 @ X3) | ~ (v2_struct_0 @ X3) | ~ (l1_orders_2 @ X3))),
% 26.70/26.90      inference('cnf', [status(esa)], [cc1_lattice3])).
% 26.70/26.90  thf('564', plain,
% 26.70/26.90      (((~ (l1_orders_2 @ sk_A) | ~ (v1_lattice3 @ sk_A)))
% 26.70/26.90         <= (~
% 26.70/26.90             ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ 
% 26.70/26.90               (k10_yellow_6 @ sk_A @ sk_B))))),
% 26.70/26.90      inference('sup-', [status(thm)], ['562', '563'])).
% 26.70/26.90  thf('565', plain, ((l1_orders_2 @ sk_A)),
% 26.70/26.90      inference('sup-', [status(thm)], ['110', '111'])).
% 26.70/26.90  thf('566', plain, ((v1_lattice3 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('567', plain,
% 26.70/26.90      (((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B)))),
% 26.70/26.90      inference('demod', [status(thm)], ['564', '565', '566'])).
% 26.70/26.90  thf('568', plain,
% 26.70/26.90      (~ ((r1_waybel_9 @ sk_A @ sk_B)) | 
% 26.70/26.90       ~
% 26.70/26.90       ((r2_hidden @ (k1_waybel_2 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B)))),
% 26.70/26.90      inference('split', [status(esa)], ['353'])).
% 26.70/26.90  thf('569', plain, (~ ((r1_waybel_9 @ sk_A @ sk_B))),
% 26.70/26.90      inference('sat_resolution*', [status(thm)], ['567', '568'])).
% 26.70/26.90  thf('570', plain, (~ (r1_waybel_9 @ sk_A @ sk_B)),
% 26.70/26.90      inference('simpl_trail', [status(thm)], ['354', '569'])).
% 26.70/26.90  thf('571', plain, ((v2_struct_0 @ sk_A)),
% 26.70/26.90      inference('clc', [status(thm)], ['352', '570'])).
% 26.70/26.90  thf('572', plain,
% 26.70/26.90      (![X3 : $i]:
% 26.70/26.90         (~ (v1_lattice3 @ X3) | ~ (v2_struct_0 @ X3) | ~ (l1_orders_2 @ X3))),
% 26.70/26.90      inference('cnf', [status(esa)], [cc1_lattice3])).
% 26.70/26.90  thf('573', plain, ((~ (l1_orders_2 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 26.70/26.90      inference('sup-', [status(thm)], ['571', '572'])).
% 26.70/26.90  thf('574', plain, ((l1_orders_2 @ sk_A)),
% 26.70/26.90      inference('sup-', [status(thm)], ['110', '111'])).
% 26.70/26.90  thf('575', plain, ((v1_lattice3 @ sk_A)),
% 26.70/26.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.70/26.90  thf('576', plain, ($false),
% 26.70/26.90      inference('demod', [status(thm)], ['573', '574', '575'])).
% 26.70/26.90  
% 26.70/26.90  % SZS output end Refutation
% 26.70/26.90  
% 26.70/26.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
